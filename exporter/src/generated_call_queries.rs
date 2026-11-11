//! Compiler metadata for helper-internal Miri calls that do not have a MIR
//! `Call` terminator. The exact synthesized caller signature is interned as a
//! source FnPtr so `compiler_function_facts.helper_signatures` emits its
//! `fn_abi_of_fn_ptr` query; target transfers use the same ABI/covariance path
//! as ordinary calls without changing runtime candidate selection.
use super::*;

fn closed(ty: ty::Ty<'_>) -> bool {
    !ty.has_non_region_param()
        && !ty.has_escaping_bound_vars()
        && !ty.has_infer()
        && !ty.has_placeholders()
        && !ty.references_error()
}

/// Record the payload type that Miri retains after `check_shim_sig` has checked
/// and transmuted the source call argument to the shim's declared ABI type.
/// This is deliberately the post-check type, not the potentially different
/// raw MIR operand type. The later catch_unwind helper consumes this type with
/// its exact source callback and data operands.
pub(super) fn register_unwind_payload_type<'tcx>(
    context: &mut ExportContext<'tcx>,
    payload: ty::Ty<'tcx>,
) {
    if closed(payload) {
        context.runtime_unwind_payload_types.insert(payload);
    }
}

/// Register one source-constructed call and its transfer facts for a concrete
/// compiler target. `args` and `destination` are the exact ImmTy/MPlaceTy
/// layouts passed by the Miri helper. No type is inferred from a same-sized
/// signature or ABI row.
pub(super) fn register_target_call<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    target: ty::Instance<'tcx>,
    args: Vec<ty::Ty<'tcx>>,
    destination: ty::Ty<'tcx>,
    caller_abi: rustc_abi::ExternAbi,
    runtime_abi_env: ty::TypingEnv<'tcx>,
) -> Result<(), String> {
    Ok::<_, String>({
        if !closed(destination) || args.iter().any(|arg| !closed(*arg)) {
            return Ok(());
        }
        context.register_instance(target);
        let signature = tcx.mk_fn_sig(
            args.iter().copied(),
            destination,
            ty::FnSigKind::default()
                .set_abi(caller_abi)
                .set_safety(rustc_hir::Safety::Safe),
        );
        context.helper_signature_requests.insert(signature);
        let function_ty = ty::Ty::new_fn_ptr(tcx, ty::Binder::dummy(signature));
        let _ = type_json(context, tcx, function_ty)?;
        if target.def.requires_caller_location(tcx) {
            let tracked_signature = tcx.mk_fn_sig(
                args.iter()
                    .copied()
                    .chain(std::iter::once(tcx.caller_location_ty())),
                destination,
                ty::FnSigKind::default()
                    .set_abi(caller_abi)
                    .set_safety(rustc_hir::Safety::Safe),
            );
            context.helper_signature_requests.insert(tracked_signature);
            let tracked_function_ty = ty::Ty::new_fn_ptr(tcx, ty::Binder::dummy(tracked_signature));
            let _ = type_json(context, tcx, tracked_function_ty)?;
        }
        let request = CallTransferRequest {
            function_ty,
            runtime_abi_env,
            caller_instance: None,
            caller_args: args,
            extra_types: ty::List::empty(),
            return_destination: destination,
            generated_caller_abi: Some(caller_abi),
        };
        register_call_transfer_for_target(context, tcx, &request, target, None, false)?;
    })
}

/// Retain a catch_unwind intrinsic's exact callback/data operand types.
/// `unwind.rs::handle_catch_unwind` calls the callbacks later, outside the MIR
/// terminator collector, after a payload has been placed in the thread state.
pub(super) fn register_catch_unwind_site<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
) -> Result<(), String> {
    Ok::<_, String>({
        if args.len() != 3 {
            return Ok(());
        }
        let try_ty = args[0].node.ty(body, tcx);
        let data_ty = args[1].node.ty(body, tcx);
        let catch_ty = args[2].node.ty(body, tcx);
        if !closed(try_ty) || !closed(data_ty) || !closed(catch_ty) {
            return Ok(());
        }
        let _ = type_json(context, tcx, try_ty)?;
        let _ = type_json(context, tcx, data_ty)?;
        let _ = type_json(context, tcx, catch_ty)?;
        context
            .runtime_catch_unwind_sites
            .insert((try_ty, data_ty, catch_ty));
    })
}

/// Materialize exact callback calls after each body-discovery wave. Payload
/// types come from the source-checked unwind shim ABI; a catch callback is not
/// guessed to receive a byte pointer or any target-dependent host type.
pub(super) fn register_catch_unwind_transfers<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<(), String> {
    let frontier = context.catch_unwind_frontier;
    let sites = context.runtime_catch_unwind_sites.len();
    let payloads = context.runtime_unwind_payload_types.len();
    for site in frontier.site_start(payloads)..sites {
        let (try_ty, data_ty, catch_ty) = *context.runtime_catch_unwind_sites.get_index(site).unwrap();
        if site >= frontier.sites {
            register_runtime_callback_call_types(
                context, tcx, "miri_catch_unwind_try".to_owned(), try_ty,
                vec![data_ty], tcx.types.unit, rustc_abi::ExternAbi::Rust,
            )?;
        }
        for payload_index in frontier.target_start(site)..payloads {
            let payload_ty = *context.runtime_unwind_payload_types.get_index(payload_index).unwrap();
            register_runtime_callback_call_types(
                context, tcx, "miri_catch_unwind_catch".to_owned(), catch_ty,
                vec![data_ty, payload_ty], tcx.types.unit, rustc_abi::ExternAbi::Rust,
            )?;
        }
    }
    context.catch_unwind_frontier.complete(sites, payloads);
    Ok(())
}

/// Shared request constructor for callbacks whose exact target identities are
/// registered elsewhere. It records only the generated source FnPtr and its
/// concrete argument/result types; caller ABI remains explicit.
pub(super) fn register_runtime_callback_call_types<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    source_symbol: String,
    callback_operand_type: ty::Ty<'tcx>,
    caller_args: Vec<ty::Ty<'tcx>>,
    return_destination: ty::Ty<'tcx>,
    caller_abi: rustc_abi::ExternAbi,
) -> Result<(), String> {
    Ok::<_, String>({
        if !closed(callback_operand_type)
            || caller_args.iter().any(|input| !closed(*input))
            || !closed(return_destination)
        {
            return Ok(());
        }
        let key = (
            source_symbol.clone(),
            callback_operand_type,
            caller_args.clone(),
            return_destination,
        );
        if !context.runtime_callback_transfer_keys.insert(key) {
            return Ok(());
        }
        let signature = tcx.mk_fn_sig(
            caller_args.iter().copied(),
            return_destination,
            ty::FnSigKind::default()
                .set_abi(caller_abi)
                .set_safety(rustc_hir::Safety::Safe),
        );
        context.helper_signature_requests.insert(signature);
        let function_ty = ty::Ty::new_fn_ptr(tcx, ty::Binder::dummy(signature));
        let _ = type_json(context, tcx, callback_operand_type)?;
        let _ = type_json(context, tcx, function_ty)?;
        context
            .runtime_callback_transfers
            .push(RuntimeCallbackTransferRequest {
                source_symbol,
                callback_operand_type,
                request: CallTransferRequest {
                    function_ty,
                    runtime_abi_env: ty::TypingEnv::fully_monomorphized(),
                    caller_instance: None,
                    caller_args,
                    extra_types: ty::List::empty(),
                    return_destination,
                    generated_caller_abi: Some(caller_abi),
                },
            });
    })
}
