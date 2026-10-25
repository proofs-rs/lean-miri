//! Exact util/compare_types.rs::relate_types(Covariant) query evidence.
//! Canonical normalized identity chooses one finite request domain, not
//! answers. Exact MIR transmute/subtype cast pairs and reached vtable receiver
//! pairs add source-demanded requests outside that domain. Every recorded
//! answer comes from the actual rustc relation query; no layout-based answer
//! is fabricated.
use super::*;
fn closed(input:ty::Ty<'_>)->bool {
    !input.has_non_region_param() && !input.has_escaping_bound_vars() &&
        !input.has_infer() && !input.has_placeholders() && !input.references_error()
}
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let env=ty::TypingEnv::fully_monomorphized();
    let mut inputs=context.type_ids.iter().map(|(ty,id)|(*id,*ty)).collect::<Vec<_>>();
    inputs.sort_by_key(|(id,_)|*id);
    let mut groups:HashMap<ty::Ty<'tcx>,Vec<ty::Ty<'tcx>>>=HashMap::new();
    for (_,input) in inputs {
        if input.has_non_region_param() || input.has_escaping_bound_vars() || input.has_infer() || input.has_placeholders() || input.references_error(){continue}
        if let Ok(normal)=tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(input)){
            groups.entry(normal).or_default().push(input);
        }
    }
    let mut pairs=groups.values().flat_map(|group|group.iter().flat_map(|a|group.iter().filter(move|b|*b!=a).map(move|b|(*a,*b)))).collect::<Vec<_>>();

    // rustc's Transmute/Subtype/BoxDerefTransmute evaluator calls
    // copy_op_allow_transmute, which still checks mir_assign_valid_types
    // (interpret/cast.rs, place.rs, eval_context.rs). Export the exact MIR
    // operand and cast-target pair even when normalization puts them in
    // different identity groups; do not infer the relation from layouts.
    for (source,target) in context.covariance_query_requests.iter().copied() {
        if source != target && closed(source) && closed(target) {
            pairs.push((source,target));
        }
    }

    // call.rs passes a virtual receiver through `copy_op_allow_transmute`.
    // place.rs still calls mir_assign_valid_types on the source and callee
    // argument layouts before honoring allow_transmute. The actual source
    // operand is the raw mutable pointer used to invoke the vtable entry; the
    // destination type comes from that concrete method's first FnAbi argument.
    // Query only these compiler-derived pairs from reached vtable metadata.
    let mut vtable_requests=context.vtable_query_requests.iter().copied().collect::<Vec<_>>();
    vtable_requests.sort_by_key(|(input,predicates)|format!("{input:?}|{predicates:?}"));
    for (input,predicates) in vtable_requests {
        if !closed(input) || predicates.has_non_region_param() || predicates.has_escaping_bound_vars() ||
            predicates.has_infer() || predicates.has_placeholders() || predicates.references_error() {
            continue;
        }
        let Some(principal)=predicates.principal().map(|principal|
            tcx.instantiate_bound_regions_with_erased(principal)) else { continue };
        let entries=tcx.vtable_entries(principal.with_self_ty(tcx,input));
        for entry in entries.iter() {
            let ty::VtblEntry::Method(instance)=*entry else { continue };
            let source=ty::Ty::new_mut_ptr(tcx,input);
            let query=(instance,ty::List::empty());
            if let Ok(abi)=tcx.fn_abi_of_instance(env.as_query_input(query)) {
                if let Some(receiver)=abi.args.first() {
                    let target=receiver.layout.ty;
                    if closed(target) && source!=target { pairs.push((source,target)); }
                }
            }
        }
    }
    pairs.sort_by_key(|(source,target)|(
        format!("{source:?}"),format!("{target:?}")));
    pairs.dedup();
    pairs.sort_by_key(|(a,b)|(context.type_id(*a),context.type_id(*b)));
    Value::Array(pairs.into_iter().map(|(source,target)|json!({
        "typing_env":"fully_monomorphized","variance":"covariant",
        // These are inputs to a projected relation query. Their genuine
        // runtime type-query demand is registered by source MIR/cast/vtable
        // discovery; a normalized-equivalence pair must not promote a
        // query-generated pointer/reference node back into the demand set.
        // query_generated_type_json still exports the complete type node.
        "source_type":query_generated_type_json(context,tcx,source),
        "target_type":query_generated_type_json(context,tcx,target),
        "status":"supported","value":rustc_const_eval::util::relate_types(tcx,env,ty::Variance::Covariant,source,target),
    })).collect())
}
