//! Finite module edges and type-alias declarations used by startup type names.
//! These rows describe source definitions; they are not resolved layout queries.
use super::*;
use rustc_hir::def::{DefKind, Res};

impl<'tcx> Material<'tcx> {
    pub(super) fn named_type_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let mut roots = Vec::new();
        let mut modules = Vec::new();
        let mut aliases = Vec::new();
        for krate in tcx.crates(()).iter().copied() {
            if tcx.crate_name(krate).as_str() != "core" { continue; }
            let root = krate.as_def_id();
            let root_id = self.definition(tcx, root);
            roots.push(json!({"name":"core","definition":root_id}));
            for child in tcx.module_children(root).iter() {
                let Res::Def(DefKind::Mod, module) = child.res else { continue; };
                if child.ident.name.as_str() != "ffi" { continue; }
                let module_id = self.definition(tcx, module);
                modules.push(json!({"parent":root_id,"name":"ffi","definition":module_id}));
                for item in tcx.module_children(module).iter() {
                    let Res::Def(DefKind::TyAlias, alias) = item.res else { continue; };
                    let alias_id = self.definition(tcx, alias);
                    let parameters = tcx.generics_of(alias);
                    let rhs = if parameters.count() == 0 {
                        Some(self.ty(tcx, tcx.type_of(alias).instantiate_identity().skip_normalization())?)
                    } else { None };
                    aliases.push(json!({"parent":module_id,"name":item.ident.name.as_str(),
                        "definition":alias_id,"generic_parameter_count":parameters.count(),"rhs":rhs}));
                }
            }
        }
        Ok(json!({"roots":roots,"modules":modules,"aliases":aliases}))
    }
}
