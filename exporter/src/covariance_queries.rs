//! Exact util/compare_types.rs::relate_types(Covariant) query evidence.
//! Canonical normalized identity chooses one finite request domain, not
//! answers. Exact MIR transmute/subtype casts, shared reborrows and vtable receiver
//! pairs add source-demanded requests outside that domain. Every recorded
//! answer comes from the actual rustc relation query; no layout-based answer
//! is fabricated.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct Query {
    typing_env: &'static str,
    variance: &'static str,
    source_type: u64,
    target_type: u64,
    value: bool,
}
fn closed(input: ty::Ty<'_>) -> bool {
    !input.has_non_region_param()
        && !input.has_escaping_bound_vars()
        && !input.has_infer()
        && !input.has_placeholders()
        && !input.references_error()
}

// A declaration-grammar capability check. It reads raw field types, never
// variances_of, a subtype relation, normalization or a layout answer.
fn raw_variance_source<'tcx>(tcx: TyCtxt<'tcx>, definition: rustc_hir::def_id::DefId,
    seen: &mut HashSet<rustc_hir::def_id::DefId>, fuel: usize) -> bool {
    if fuel == 0 { return false; }
    if !seen.insert(definition) { return true; }
    let adt = tcx.adt_def(definition);
    let arguments = ty::GenericArgs::identity_for_item(tcx, definition);
    adt.all_fields().all(|field|
        raw_variance_type(tcx, field.ty(tcx, arguments).skip_norm_wip(), seen, fuel - 1))
}
fn raw_variance_type<'tcx>(tcx: TyCtxt<'tcx>, input: ty::Ty<'tcx>,
    seen: &mut HashSet<rustc_hir::def_id::DefId>, fuel: usize) -> bool {
    if fuel == 0 { return false; }
    match input.kind() {
        ty::Bool | ty::Char | ty::Str | ty::Never | ty::Int(_) | ty::Uint(_) |
        ty::Float(_) | ty::Param(_) => true,
        ty::Ref(_, child, _) | ty::RawPtr(child, _) | ty::Slice(child) =>
            raw_variance_type(tcx, *child, seen, fuel - 1),
        ty::Pat(child, pattern) if matches!(*pattern.0, ty::PatternKind::NotNull) =>
            raw_variance_type(tcx, *child, seen, fuel - 1),
        ty::Array(child, length) => matches!(length.kind(), ty::ConstKind::Param(_) | ty::ConstKind::Value(_)) &&
            raw_variance_type(tcx, *child, seen, fuel - 1),
        ty::Tuple(fields) => fields.iter().all(|field| raw_variance_type(tcx, field, seen, fuel - 1)),
        ty::Adt(adt, arguments) => raw_variance_source(tcx, adt.did(), seen, fuel - 1) &&
            arguments.iter().all(|argument| match argument.kind() {
                ty::GenericArgKind::Type(ty) => raw_variance_type(tcx, ty, seen, fuel - 1),
                ty::GenericArgKind::Lifetime(_) => true,
                ty::GenericArgKind::Const(value) => matches!(value.kind(), ty::ConstKind::Param(_) | ty::ConstKind::Value(_)),
            }),
        ty::FnPtr(types, header) => {
            let signature = types.with(*header);
            signature.bound_vars().iter().all(|variable| matches!(variable, ty::BoundVariableKind::Region(_))) &&
                signature.skip_binder().inputs_and_output.iter().all(|ty| raw_variance_type(tcx, ty, seen, fuel - 1))
        },
        _ => false,
    }
}

// This recognizes the raw-syntax domain implemented by Lean's
// CompilerCovariance.structural. It never evaluates the compiler relation.
// Nominal variance uses only the raw declaration grammar above. Aliases,
// binders and non-erased relation regions retain exact residual rows.
fn lean_structural_domain<'tcx>(tcx: TyCtxt<'tcx>, a: ty::Ty<'tcx>, b: ty::Ty<'tcx>, fuel: usize) -> bool {
    if fuel == 0 { return false; }
    if a == b { return true; }
    match (a.kind(), b.kind()) {
        (ty::Bool | ty::Char | ty::Never | ty::Str | ty::Int(_) | ty::Uint(_) | ty::Float(_),
         ty::Bool | ty::Char | ty::Never | ty::Str | ty::Int(_) | ty::Uint(_) | ty::Float(_)) => true,
        (ty::RawPtr(a, am), ty::RawPtr(b, bm)) => am != bm || lean_structural_domain(tcx, *a, *b, fuel - 1),
        (ty::Ref(ar, a, am), ty::Ref(br, b, bm)) if matches!(ar.kind(),ty::ReStatic | ty::ReErased) && matches!(br.kind(),ty::ReStatic | ty::ReErased) =>
            am != bm || lean_structural_domain(tcx, *a, *b, fuel - 1),
        (ty::Slice(a), ty::Slice(b)) => lean_structural_domain(tcx, *a, *b, fuel - 1),
        (ty::Array(a, ac), ty::Array(b, bc)) => ac == bc && lean_structural_domain(tcx, *a, *b, fuel - 1),
        (ty::Tuple(a), ty::Tuple(b)) => a.len() != b.len() ||
            a.iter().zip(b.iter()).all(|(a,b)| lean_structural_domain(tcx,a,b,fuel - 1)),
        (ty::Adt(a, aa), ty::Adt(b, ba)) => {
            if a.did() != b.did() { return true; }
            aa.len() == ba.len() && raw_variance_source(tcx, a.did(), &mut HashSet::new(), fuel - 1) &&
                aa.iter().zip(ba.iter()).all(|(a,b)| match (a.kind(),b.kind()) {
                    (ty::GenericArgKind::Type(a),ty::GenericArgKind::Type(b)) =>
                        lean_structural_domain(tcx,a,b,fuel - 1),
                    (ty::GenericArgKind::Lifetime(a),ty::GenericArgKind::Lifetime(b)) => matches!(a.kind(),ty::ReStatic | ty::ReErased) && matches!(b.kind(),ty::ReStatic | ty::ReErased),
                    (ty::GenericArgKind::Const(a),ty::GenericArgKind::Const(b)) => a == b,
                    _ => false,
                })
        },
        (ty::Foreign(_), ty::Foreign(_)) => true,
        _ => false,
    }
}
// Discovery runs inside the export fixed point because serializing a demanded
// endpoint can recursively add types, predicates, instances and allocations.
// Normalized identity pairs use types already in the pool and add no endpoints.
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut pairs = std::mem::take(&mut context.covariance_pairs);
    let pair_start = pairs.len();
    // rustc's Transmute/Subtype/BoxDerefTransmute and shared Reborrow evaluators call
    // copy_op_allow_transmute, which still checks mir_assign_valid_types
    // (interpret/cast.rs, place.rs, eval_context.rs). Export the exact MIR
    // operand and cast-target pair even when normalization puts them in
    // different identity groups; do not infer the relation from layouts.
    for (source, target) in context.covariance_query_requests.suffix(context.covariance_pair_cursor).iter().copied() {
        if source != target && closed(source) && closed(target) {
            pairs.insert((source, target));
        }
    }

    // call.rs passes a virtual receiver through `copy_op_allow_transmute`.
    // place.rs still calls mir_assign_valid_types on the source and callee
    // argument layouts before honoring allow_transmute. The actual source
    // operand is the raw mutable pointer used to invoke the vtable entry; the
    // destination type comes from that concrete method's first FnAbi argument.
    // Query only these compiler-derived pairs from reached vtable metadata.
    context.covariance_pair_cursor = context.covariance_query_requests.len();
    let vtable_requests = context.vtable_query_requests.suffix(context.covariance_vtable_cursor).to_vec();
    context.covariance_vtable_cursor = context.vtable_query_requests.len();
    for (input, predicates) in vtable_requests {
        if !closed(input)
            || predicates.has_non_region_param()
            || predicates.has_escaping_bound_vars()
            || predicates.has_infer()
            || predicates.has_placeholders()
            || predicates.references_error()
        {
            continue;
        }
        let Some(principal) = predicates
            .principal()
            .map(|principal| tcx.instantiate_bound_regions_with_erased(principal))
        else {
            continue;
        };
        let entries = tcx.vtable_entries(principal.with_self_ty(tcx, input));
        for entry in entries.iter() {
            let ty::VtblEntry::Method(instance) = *entry else {
                continue;
            };
            let source = ty::Ty::new_mut_ptr(tcx, input);
            let target = if let Some(signature) = super::instance_abi_material::signature(tcx, instance, ty::List::empty()) {
                super::instance_abi_material::trace("vtable-receiver-source", false, instance);
                signature.inputs().first().copied()
            } else {
                super::instance_abi_material::trace("vtable-receiver-residual", true, instance);
                let query = (instance, ty::List::empty());
                let abi = tcx.fn_abi_of_instance(env.as_query_input(query))
                    .map_err(|error| format!("vtable receiver ABI query failed: {error:?}"))?;
                abi.args.first().map(|receiver| receiver.layout.ty)
            };
            if let Some(target) = target {
                if closed(target) && source != target {
                    pairs.insert((source, target));
                }
            }
        }
    }
    let ordered = pairs.suffix(pair_start).to_vec();
    for (source, target) in ordered {
        // Suppression applies recursively while exporting the complete node:
        // query-generated pointer/reference types must not become source demands.
        query_generated_type_json(context, tcx, source)?;
        query_generated_type_json(context, tcx, target)?;
    }
    context.covariance_pairs = pairs;
    Ok(())
}

// Evaluation is a read-only projection of the completed type pool. No relation
// answer is consumed by discovery, so each exact ordered pair is evaluated once.
pub(super) fn evaluate<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &ExportContext<'tcx>,
    mut pairs: HashSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
) -> Result<Vec<Query>, String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut inputs = context.type_ids.iter().map(|(ty, id)| (*id, *ty)).collect::<Vec<_>>();
    inputs.sort_by_key(|(id, _)| *id);
    let mut groups: HashMap<ty::Ty<'tcx>, Vec<ty::Ty<'tcx>>> = HashMap::new();
    for (_, input) in inputs {
        if !closed(input) {
            continue;
        }
        let normal = tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
            .map_err(|error| format!("covariance normalization failed: {error:?}"))?;
        groups.entry(normal).or_default().push(input);
    }
    for group in groups.values() {
        for &source in group {
            for &target in group {
                if source != target {
                    pairs.insert((source, target));
                }
            }
        }
    }
    let mut ordered = pairs.into_iter().map(|(source, target)| {
        let source_type = *context.type_ids.get(&source)
            .ok_or("covariance source endpoint missing after discovery")?;
        let target_type = *context.type_ids.get(&target)
            .ok_or("covariance target endpoint missing after discovery")?;
        Ok((source_type, target_type, source, target))
    }).collect::<Result<Vec<_>, String>>()?;
    ordered.sort_by_key(|(source_id, target_id, _, _)| (*source_id, *target_id));
    Ok(ordered.into_iter()
      .filter(|(source_id, target_id, source, target)| {
        let covered = lean_structural_domain(tcx, *source, *target, 16384);
        if std::env::var_os("LEAN_MIRI_TRACE_COVARIANCE_CALLS").is_some() {
            eprintln!("lean_miri_covariance_call queried={} source_id={} target_id={} source={source:?} target={target:?}", !covered, source_id, target_id);
        }
        !covered
      })
      .map(|(source_type, target_type, source, target)| Query {
        typing_env: "fully_monomorphized",
        variance: "covariant",
        source_type,
        target_type,
        value: rustc_const_eval::util::relate_types(
            tcx, env, ty::Variance::Covariant, source, target,
        ),
    }).collect())
}
