//! Exact startup preflight queries from pinned Miri eval.rs and helpers.rs.
use super::*;

use rustc_hir::def::Namespace;
use rustc_hir::def_id::CRATE_DEF_INDEX;

/// Mirrors helpers::try_resolve_did / try_resolve_path, including crate-name
/// iteration order, module-only intermediate segments, and final namespace.
fn resolve_path<'tcx>(tcx: TyCtxt<'tcx>, path: &[&str], namespace: Namespace)
    -> Option<rustc_hir::def_id::DefId>
{
    let (&crate_name, path) = path.split_first()?;
    let (&item_name, modules) = path.split_last()?;
    'crates: for crate_num in tcx.crates(()).iter()
        .filter(|&&crate_num| tcx.crate_name(crate_num).as_str() == crate_name)
    {
        let mut current = rustc_hir::def_id::DefId {
            krate: *crate_num,
            index: CRATE_DEF_INDEX,
        };
        for segment in modules {
            let symbol = rustc_span::Symbol::intern(segment);
            let next = tcx.module_children(current).iter()
                .filter(|child| child.ident.name == symbol)
                .map(|child| child.res.def_id())
                .find(|&child| tcx.def_kind(child) == rustc_hir::def::DefKind::Mod);
            let Some(next) = next else { continue 'crates };
            current = next;
        }
        let symbol = rustc_span::Symbol::intern(item_name);
        if let Some(item) = tcx.module_children(current).iter()
            .filter(|child| child.ident.name == symbol)
            .map(|child| child.res.def_id())
            .find(|&child| tcx.def_kind(child).ns() == Some(namespace))
        {
            return Some(item);
        }
    }
    None
}

pub(super) fn export(tcx: TyCtxt<'_>) -> Value {
    // Exact helpers::is_no_core: rustc_attr_ir::find_attr!(tcx, crate, NoCore).
    let no_core = rustc_attr_ir::find_attr!(tcx, crate, NoCore);
    let core_escape_default = match resolve_path(
        tcx,
        &["core", "ascii", "escape_default"],
        Namespace::ValueNS,
    ) {
        Some(definition) => compiler_fact(json!({
            "definition": def_json(definition),
            "mir_available": tcx.is_mir_available(definition),
        })),
        None => json!({
            "status":"unsupported",
            "reason":"source try_resolve_path did not find core::ascii::escape_default in the value namespace",
        }),
    };
    json!({
        "no_core":compiler_fact(json!(no_core)),
        "core_escape_default":core_escape_default,
    })
}
