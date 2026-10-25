//! helpers.rs::eval_path / eval_global compiler evidence for pthread globals.
//! These are path queries, not guessed from host bytes or runtime lifecycle.
use super::*;

fn query<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>, name: &str) -> Value {
    let path = ["libc", name];
    let instance = match shim_abi::named_instance(tcx, &path, rustc_hir::def::Namespace::ValueNS) {
        Ok(instance) => instance,
        Err(reason) => return json!({"status":"unsupported","reason":reason}),
    };
    let def = instance.def_id();
    let kind = tcx.def_kind(def);
    if !matches!(kind, rustc_hir::def::DefKind::Const | rustc_hir::def::DefKind::AssocConst
        | rustc_hir::def::DefKind::Static { .. }) {
        return json!({"status":"unsupported","reason":format!("named libc path resolved to non-global item kind {kind:?}")});
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let value_ty = instance.ty(tcx, env);
    let (allocation_kind, alloc_id) = if tcx.is_static(def) {
        ("static", tcx.reserve_and_set_static_alloc(def))
    } else {
        let global = rustc_middle::mir::interpret::GlobalId { instance, promoted: None };
        match tcx.at(rustc_span::DUMMY_SP).eval_to_allocation_raw(env.as_query_input(global)) {
            Ok(value) => ("const_allocation", value.alloc_id),
            Err(error) => {
                return json!({"status":"unsupported","reason":"compiler eval_global constant allocation query failed",
                    "error_debug":format!("{error:?}")});
            }
        }
    };
    let allocation = allocation_ref(context, tcx, alloc_id);
    let allocation_supported = allocation_status(context, &allocation) == "supported";
    let type_ref = type_json(context, tcx, value_ty);
    let status = if allocation_supported { "supported" } else { "unsupported" };
    json!({"status":status,"value":{
        "definition":def_json(def),
        "kind":allocation_kind,
        "type":type_ref,
        "allocation":allocation
    },"reason":if allocation_supported { Value::Null } else { json!("compiler global allocation image is unavailable") }})
}

pub(super) fn export<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>) -> Value {
    let names = [
        "PTHREAD_MUTEX_INITIALIZER",
        "PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP",
        "PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_RWLOCK_INITIALIZER",
        "PTHREAD_COND_INITIALIZER",
    ];
    Value::Array(names.into_iter().map(|name| json!({
        "name":name,
        "path":["libc",name],
        "typing_env":"fully_monomorphized",
        "query":query(tcx,context,name)
    })).collect())
}
