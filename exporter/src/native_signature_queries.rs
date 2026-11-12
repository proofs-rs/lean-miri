//! Exact native callback FnSig query, alloc_addresses/mod.rs:167–174.
//! No normalization or ABI lowering is substituted for the pinned query.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct Query {
    instance_id: u64,
    query: &'static str,
    normalization: &'static str,
    bound_regions: &'static str,
    signature_query: pool_type::FunctionSignature,
}
pub(super) fn discover<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut State,
) -> Result<(), String> {
    let mut seen = HashSet::new();
    let mut requests = context.instance_events[state.events..].iter().copied()
        .filter(|instance| seen.insert(*instance))
        .filter(|instance| !context.runtime_query_only_empty_drops.contains(instance)
            && !context.symbol_only_instances.contains(instance)
            && !matches!(instance.def, ty::InstanceKind::Virtual(..)))
        .filter(|instance| {
            let kind = tcx.def_kind(instance.def_id());
            kind.is_fn_like() || matches!(kind,
                rustc_hir::def::DefKind::Ctor(_, rustc_hir::def::CtorKind::Fn))
        })
        .map(|instance| (context.instance_ids[&instance], instance))
        .filter(|(id, _)| !state.facts.contains_key(id))
        .collect::<Vec<_>>();
    state.events = context.instance_events.len();
    requests.sort_by_key(|(id, _)| *id);
    let facts = requests.into_iter().map(|(id,instance)| { {
        let closed=!instance.args.has_non_region_param() && !instance.args.has_escaping_bound_vars()
            && !instance.args.has_infer() && !instance.args.has_placeholders() && !instance.args.references_error();
        let def_kind=tcx.def_kind(instance.def_id());
        let callable=def_kind.is_fn_like()
            || matches!(def_kind,rustc_hir::def::DefKind::Ctor(_,rustc_hir::def::CtorKind::Fn));
        let (signature,query)=if !closed || !callable {
            (export_failure("native FnSig", format!("requires closed callable instance: {instance:?} (closed={closed}, callable={callable})"))?,
                "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))")
        } else if matches!(def_kind, rustc_hir::def::DefKind::Closure | rustc_hir::def::DefKind::SyntheticCoroutineBody) {
            // Closure DefIds do not have a standalone `fn_sig` metadata entry.
            // Their exact call signature is encoded in the closure generic args.
            let closure_ty=instance.ty(tcx,ty::TypingEnv::fully_monomorphized());
            match closure_ty.kind() {
                ty::Closure(_,args)=>{
                    let sig=tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
                    (compiler_fact(fn_sig_json_inner(context,tcx,sig)?),
                        "instantiate_bound_regions_with_erased(closure_args.sig())")
                }
                // Coroutine bodies have their adjusted resume/poll signature
                // only in fn_sig_for_fn_abi. That is not this native callback
                // query (alloc_addresses/mod.rs:167–174); never substitute ABI
                // lowering for a compiler FnSig. A real native callback demand
                // for an absent row remains fail-closed in the consumer.
                ty::Coroutine(..) | ty::CoroutineClosure(..) => return Ok(None),
                _=>(unavailable_compiler_fact("closure instance type does not carry a normal closure FnSig")?,
                    "closure_args.sig() unavailable for non-closure instance type")
            }
        } else {
            let sig=tcx.instantiate_bound_regions_with_erased(
                tcx.fn_sig(instance.def_id()).instantiate(tcx,instance.args).skip_norm_wip());
            (compiler_fact(fn_sig_json_inner(context,tcx,sig)?),
                "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))")
        };
        Ok::<_, String>(Some(SignatureFact { instance_id: id, query, signature }))
    } }).collect::<Result<Vec<_>, String>>()?;
    for fact in facts.into_iter().flatten() { state.facts.insert(fact.instance_id, fact); }
    Ok(())
}

// Discovery owns all signature serialization; finalization only projects the
// retained facts into the public query schema.
pub(super) struct SignatureFact {
    instance_id: u64,
    query: &'static str,
    signature: pool_type::FunctionSignature,
}
#[derive(Default)]
pub(super) struct State {
    events: usize,
    facts: BTreeMap<u64, SignatureFact>,
}
pub(super) fn finish(state: State, context: &ExportContext<'_>) -> Vec<Query> {
    state.facts.into_values().filter(|fact| {
        let instance = context.instance_ids.key(fact.instance_id as usize).unwrap();
        !context.symbol_only_instances.contains(instance)
            && !context.runtime_query_only_empty_drops.contains(instance)
    }).map(|fact| Query {
        instance_id: fact.instance_id,
        query: fact.query,
        normalization: "none",
        bound_regions: "erased",
        signature_query: fact.signature,
    }).collect()
}
