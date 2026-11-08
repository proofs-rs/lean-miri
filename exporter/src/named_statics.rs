//! helpers.rs::eval_path / eval_global compiler evidence for pthread globals.
//! These are path queries, not guessed from host bytes or runtime lifecycle.
use super::*;

fn query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    name: &str,
) -> Result<Value, String> {
    let path = ["libc", name];
    let instance = match shim_abi::named_instance(tcx, &path, rustc_hir::def::Namespace::ValueNS) {
        Ok(instance) => instance,
        Err(reason) => {
            return Ok(export_failure(
                "named_statics::query",
                format!("{}", reason),
            )?);
        }
    };
    let def = instance.def_id();
    let kind = tcx.def_kind(def);
    if !matches!(
        kind,
        rustc_hir::def::DefKind::Const
            | rustc_hir::def::DefKind::AssocConst
            | rustc_hir::def::DefKind::Static { .. }
    ) {
        return Ok(export_failure(
            "named_statics::query",
            format!(
                "{}",
                format!("named libc path resolved to non-global item kind {kind:?}")
            ),
        )?);
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let value_ty = instance.ty(tcx, env);
    let (allocation_kind, alloc_id) = if tcx.is_static(def) {
        ("static", tcx.reserve_and_set_static_alloc(def))
    } else {
        let global = rustc_middle::mir::interpret::GlobalId {
            instance,
            promoted: None,
        };
        match tcx
            .at(rustc_span::DUMMY_SP)
            .eval_to_allocation_raw(env.as_query_input(global))
        {
            Ok(value) => ("const_allocation", value.alloc_id),
            Err(error) => {
                return Ok(export_failure(
                    "named_statics::query",
                    format!(
                        "{}; {}",
                        "compiler eval_global constant allocation query failed",
                        format!("{error:?}")
                    ),
                )?);
            }
        }
    };
    let allocation = allocation_ref(context, tcx, alloc_id)?;
    let type_ref = type_json(context, tcx, value_ty)?;
    Ok::<_, String>(json!({"status":"supported","value":{
        "definition":def_json(def),
        "kind":allocation_kind,
        "type":type_ref,
        "allocation":allocation
    }}))
}

pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Value, String> {
    if !shim_abi::is_unix_target(tcx) {
        return Ok(json!([]));
    }
    let names = [
        "PTHREAD_MUTEX_INITIALIZER",
        "PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP",
        "PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_RWLOCK_INITIALIZER",
        "PTHREAD_COND_INITIALIZER",
    ];
    Ok::<_, String>(Value::Array(
        names
            .into_iter()
            .filter(|name| {
                // unix/sync.rs::mutex_init_offset only checks the NP forms on Linux.
                !name.ends_with("_NP") || tcx.sess.target.os == rustc_target::spec::Os::Linux
            })
            .map(|name| {
                Ok::<_, String>(json!({
                    "name":name,
                    "path":["libc",name],
                    "typing_env":"fully_monomorphized",
                    "query":query(tcx,context,name)?
                }))
            })
            .collect::<Result<Vec<_>, String>>()?,
    ))
}
