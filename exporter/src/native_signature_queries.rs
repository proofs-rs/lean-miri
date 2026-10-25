//! Exact native callback FnSig query, alloc_addresses/mod.rs:167–174.
//! No normalization or ABI lowering is substituted for the pinned query.
use super::*;
pub(super) fn export<'tcx>(tcx:TyCtxt<'tcx>,context:&mut ExportContext<'tcx>)->Value {
    let mut requests=context.instance_ids.iter()
        .filter(|(instance,_)| !context.runtime_query_only_empty_drops.contains(instance))
        .map(|(instance,id)|(*id,*instance)).collect::<Vec<_>>();
    requests.sort_by_key(|(id,_)|*id);
    Value::Array(requests.into_iter().map(|(id,instance)| {
        let closed=!instance.args.has_non_region_param() && !instance.args.has_escaping_bound_vars()
            && !instance.args.has_infer() && !instance.args.has_placeholders() && !instance.args.references_error();
        let def_kind=tcx.def_kind(instance.def_id());
        let callable=def_kind.is_fn_like()
            || matches!(def_kind,rustc_hir::def::DefKind::Ctor(_,rustc_hir::def::CtorKind::Fn));
        let (signature,query)=if !closed || !callable {
            (unavailable_compiler_fact("native FnSig requires a complete compiler function instance"),
                "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))")
        } else if def_kind==rustc_hir::def::DefKind::Closure {
            // Closure DefIds do not have a standalone `fn_sig` metadata entry.
            // Their exact call signature is encoded in the closure generic args.
            let closure_ty=instance.ty(tcx,ty::TypingEnv::fully_monomorphized());
            match closure_ty.kind() {
                ty::Closure(_,args)=>{
                    let sig=tcx.instantiate_bound_regions_with_erased(args.as_closure().sig());
                    (compiler_fact(fn_sig_json_inner(context,tcx,sig)),
                        "instantiate_bound_regions_with_erased(closure_args.sig())")
                }
                _=>(unavailable_compiler_fact("closure instance type does not carry a normal closure FnSig"),
                    "closure_args.sig() unavailable for non-closure instance type")
            }
        } else {
            let sig=tcx.instantiate_bound_regions_with_erased(
                tcx.fn_sig(instance.def_id()).instantiate(tcx,instance.args).skip_norm_wip());
            (compiler_fact(fn_sig_json_inner(context,tcx,sig)),
                "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))")
        };
        json!({"instance_id":id,
            "instance_kind":instance_kind_json(context,tcx,instance.def),
            "generic_args":generic_args_json(context,tcx,instance.args),
            "query":query,
            "normalization":"none","bound_regions":"erased",
            "signature_query":signature})
    }).collect())
}
