//! Definition-scoped symbol inputs. Never calls symbol_name(instance), selects
//! an instance, or computes a mangled name. Foreign module linkage is finite
//! crate declaration data; the consumer applies target-dependent precedence.
use super::*;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;

impl<'tcx> Material<'tcx> {
    pub(super) fn symbol_name_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let mut definitions = self.def_ids.iter().map(|(&definition,&index)|(index,definition))
            .filter(|(_,definition)|tcx.def_kind(*definition).has_codegen_attrs()).collect::<Vec<_>>();
        definitions.sort_by_key(|(index,_)|*index);
        let mut modules: Vec<(DefId,Option<String>)> = Vec::new();
        let mut declarations = Vec::new();
        for (index,definition) in definitions {
            let attrs = tcx.codegen_fn_attrs(definition);
            let foreign_item = tcx.is_foreign_item(definition);
            let (foreign_module,wasm_import_module) = if foreign_item {
                let parent = tcx.parent(definition);
                let module = if let Some((_,module)) = modules.iter().find(|(owner,_)|*owner==parent) {
                    module.clone()
                } else {
                    // symbol_export::wasm_import_module_map first collects the
                    // complete native-library source list by foreign module.
                    // Its map insertion gives the last declaration precedence.
                    // Preserve that same module attribute, without invoking
                    // the symbol map or the per-instance naming query.
                    let module = tcx.native_libraries(definition.krate).iter()
                        .filter(|library|library.foreign_module==Some(parent)).last()
                        .and_then(|library|library.wasm_import_module())
                        .map(|name|name.as_str().to_owned());
                    modules.push((parent,module.clone()));
                    module
                };
                (Some(self.definition(tcx,parent)),module)
            } else { (None,None) };
            declarations.push(json!({"definition":index,"foreign_item":foreign_item,
                "foreign_module":foreign_module,"wasm_import_module":wasm_import_module,
                "attributes":{
                    // CodegenFnAttrs::symbol_name is the parsed export_name /
                    // link_name (or language-item linkage attribute), not a
                    // monomorphized/mangled symbol_name query result.
                    "symbol_name":attrs.symbol_name.map(|name|name.as_str().to_owned()),
                    "item_name":tcx.opt_item_name(definition).map(|name|name.as_str().to_owned()),
                    "no_mangle":attrs.flags.contains(F::NO_MANGLE),
                    "std_internal_symbol":attrs.flags.contains(F::RUSTC_STD_INTERNAL_SYMBOL),
                    "linkage":attrs.linkage.map(|linkage|format!("{linkage:?}")),
                    "proc_macro_declarations":definition.as_local().is_some_and(|local|
                        tcx.proc_macro_decls_static(())==Some(local))
                }}));
        }
        Ok(json!({"declarations":declarations}))
    }
}
