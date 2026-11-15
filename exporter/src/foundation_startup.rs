//! Bounded finite module source graph. No resolved startup query answer.
use std::collections::HashSet;
use rustc_hir::def::{DefKind, Namespace};
use rustc_hir::def_id::{DefId, CRATE_DEF_INDEX};
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

pub(super) fn capture(tcx: TyCtxt<'_>, mut intern: impl FnMut(DefId) -> usize)
    -> Result<Value, String> {
    let no_core = rustc_attr_ir::find_attr!(tcx, crate, NoCore);
    if no_core {
        return Ok(json!({"no_core":true,"capture_scope":"core_ascii_children",
            "module_depth":1,"crates":[],"modules":[]}));
    }
    let mut crates = Vec::new();
    let mut modules = Vec::new();
    let mut seen = HashSet::new();
    for &number in tcx.crates(()) {
        let root = DefId { krate:number, index:CRATE_DEF_INDEX };
        crates.push(json!({"crate_index":number.as_u32(),"name":tcx.crate_name(number).as_str(),"root":intern(root)}));
        // Fixed startup demand only: retain every crate name/order, then all
        // children at the core root and every ascii-named module. Do not choose
        // a winning crate/module/item here; Lean performs those ordered choices.
        if tcx.crate_name(number).as_str() != "core" { continue; }
        let mut pending = vec![root];
        for child in tcx.module_children(root) {
            if let Some(def) = child.res.opt_def_id() {
                if child.ident.name.as_str() == "ascii" && tcx.def_kind(def) == DefKind::Mod {
                    pending.push(def);
                }
            }
        }
        for module in pending {
            if !seen.insert(module) { continue; }
            let children = tcx.module_children(module).iter().map(|child| {
                let definition = child.res.opt_def_id();
                let kind = definition.map(|def|tcx.def_kind(def));
                let namespace = kind.and_then(|kind|kind.ns()).map(|ns|match ns {
                    Namespace::TypeNS=>"type",Namespace::ValueNS=>"value",Namespace::MacroNS=>"macro",
                });
                let mir_available = definition.filter(|_|namespace == Some("value"))
                    .map(|def|tcx.is_mir_available(def));
                json!({"name":child.ident.name.as_str(),"definition":definition.map(&mut intern),
                    "is_module":kind == Some(DefKind::Mod),"namespace":namespace,
                    "mir_available":mir_available})
            }).collect::<Vec<_>>();
            modules.push(json!({"definition":intern(module),"children":children}));
        }
    }
    Ok(json!({"no_core":no_core,"capture_scope":"core_ascii_children","module_depth":1,"crates":crates,"modules":modules}))
}
