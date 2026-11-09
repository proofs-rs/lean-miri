//! helpers.rs::eval_path / eval_global compiler evidence for pthread globals.
//! These are path queries, not guessed from host bytes or runtime lifecycle.
use super::*;

#[derive(serde::Serialize)]
pub(super) struct Record {
    name: &'static str,
    path: Vec<&'static str>,
    typing_env: &'static str,
    query: Query,
}
#[derive(serde::Serialize)]
struct Query {
    definition: u64,
    kind: &'static str,
    #[serde(rename = "type")]
    ty: u64,
    allocation: u64,
}
fn query<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    name: &str,
) -> Result<Query, String> {
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
    Ok(Query {
        definition: def_json(context, def),
        kind: allocation_kind,
        ty: type_ref,
        allocation,
    })
}

pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Vec<Record>, String> {
    if !shim_abi::is_unix_target(tcx) {
        return Ok(vec![]);
    }
    let names = [
        "PTHREAD_MUTEX_INITIALIZER",
        "PTHREAD_RECURSIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP",
        "PTHREAD_ADAPTIVE_MUTEX_INITIALIZER_NP",
        "PTHREAD_RWLOCK_INITIALIZER",
        "PTHREAD_COND_INITIALIZER",
    ];
    names
        .into_iter()
        .filter(|name| {
            !name.ends_with("_NP") || tcx.sess.target.os == rustc_target::spec::Os::Linux
        })
        .map(|name| {
            Ok(Record {
                name,
                path: vec!["libc", name],
                typing_env: "fully_monomorphized",
                query: query(tcx, context, name)?,
            })
        })
        .collect()
}
