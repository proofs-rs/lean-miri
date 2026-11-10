//! Exact util/compare_types.rs::relate_types(Covariant) query evidence.
//! Canonical normalized identity chooses one finite request domain, not
//! answers. Exact MIR transmute/subtype cast pairs and reached vtable receiver
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
// Discovery runs inside the export fixed point because serializing a demanded
// endpoint can recursively add types, predicates, instances and allocations.
// Normalized identity pairs use types already in the pool and add no endpoints.
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<HashSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>, String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut pairs = HashSet::new();
    // rustc's Transmute/Subtype/BoxDerefTransmute evaluator calls
    // copy_op_allow_transmute, which still checks mir_assign_valid_types
    // (interpret/cast.rs, place.rs, eval_context.rs). Export the exact MIR
    // operand and cast-target pair even when normalization puts them in
    // different identity groups; do not infer the relation from layouts.
    for (source, target) in context.covariance_query_requests.iter().copied() {
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
    let mut vtable_requests = context
        .vtable_query_requests
        .iter()
        .copied()
        .collect::<Vec<_>>();
    vtable_requests.sort_by_cached_key(|(input, predicates)| format!("{input:?}|{predicates:?}"));
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
            let query = (instance, ty::List::empty());
            let abi = tcx
                .fn_abi_of_instance(env.as_query_input(query))
                .map_err(|error| format!("vtable receiver ABI query failed: {error:?}"))?;
            if let Some(receiver) = abi.args.first() {
                let target = receiver.layout.ty;
                if closed(target) && source != target {
                    pairs.insert((source, target));
                }
            }
        }
    }
    let mut ordered = pairs.iter().copied().collect::<Vec<_>>();
    ordered.sort_by_cached_key(|(source, target)| (format!("{source:?}"), format!("{target:?}")));
    for (source, target) in ordered {
        // Suppression applies recursively while exporting the complete node:
        // query-generated pointer/reference types must not become source demands.
        query_generated_type_json(context, tcx, source)?;
        query_generated_type_json(context, tcx, target)?;
    }
    Ok(pairs)
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
    Ok(ordered.into_iter().map(|(source_type, target_type, source, target)| Query {
        typing_env: "fully_monomorphized",
        variance: "covariant",
        source_type,
        target_type,
        value: rustc_const_eval::util::relate_types(
            tcx, env, ty::Variance::Covariant, source, target,
        ),
    }).collect())
}
