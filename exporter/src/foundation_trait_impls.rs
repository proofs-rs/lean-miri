//! Reachable generic auto-trait declarations and complete manual impl syntax.
//! No selection, obligation evaluation or instantiated answer is requested.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn trait_impl_source(&mut self, tcx: TyCtxt<'tcx>, roots: &[Value]) -> Result<Value> {
        let mut pending = Vec::new();
        for root in roots {
            if let Some(layers) = root["environment"]["layers"].as_array() {
                for layer in layers { if let Some(clauses) = layer["clauses"].as_array() {
                    for clause in clauses { if clause["kind"] == "trait" {
                        if let Some(index) = clause["definition"].as_u64() {
                            if let Some((&definition,_)) = self.def_ids.iter().find(|(_,id)| **id == index as usize) {
                                if tcx.trait_is_auto(definition) {pending.push(definition);}
                            }
                        }
                    }}
                }}
            }
        }
        let mut seen = Vec::new(); let mut declarations = Vec::new();
        while let Some(definition) = pending.pop() {
            if seen.contains(&definition) {continue;} seen.push(definition);
            if seen.len() > 128 {return unsupported("reachable trait declaration budget",seen.len());}
            let generics = tcx.generics_of(definition);
            let environment = self.generic_environment(tcx,definition)?;
            let mut implementations = tcx.all_impls(definition).collect::<Vec<_>>();
            implementations.sort_by_key(|def|(def.krate.as_u32(),def.index.as_u32()));
            let mut rows = Vec::new();
            for implementation in implementations {
                let header = tcx.impl_trait_header(implementation);
                let reference = header.trait_ref.instantiate_identity().skip_normalization();
                let head = super::auto_trait_material::outer_constructor(reference.self_ty());
                let syntax = if matches!(reference.self_ty().kind(),ty::Adt(..)|ty::FnDef(..)|ty::Closure(..)|ty::CoroutineClosure(..)|ty::Coroutine(..)|ty::Dynamic(..)|ty::FnPtr(..)) {
                    Value::Null
                } else {
                    let environment = self.generic_environment(tcx,implementation)?;
                    for layer in environment["layers"].as_array().into_iter().flatten() {
                        for clause in layer["clauses"].as_array().into_iter().flatten() {
                            if clause["kind"] == "trait" && clause["lang_item"].is_null() {
                                if let Some(index) = clause["definition"].as_u64() {
                                    if let Some((&dependency,_)) = self.def_ids.iter().find(|(_,id)| **id == index as usize) {
                                        if tcx.trait_is_auto(dependency) {pending.push(dependency);}
                                    }
                                }
                            }
                        }
                    }
                    json!({"environment":environment,"self_type":self.ty(tcx,reference.self_ty())?,
                        "trait_arguments":self.args(tcx,reference.args)?,"constness":format!("{:?}",header.constness),
                        "final":tcx.defaultness(implementation).is_final()})
                };
                rows.push(json!({"definition":self.definition(tcx,implementation),"outer_head":head,
                    "polarity":format!("{:?}",header.polarity),"syntax":syntax}));
            }
            declarations.push(json!({"definition":self.definition(tcx,definition),"is_auto":tcx.trait_is_auto(definition),
                "environment":environment,"implementations":rows,"has_self":generics.has_self,
                "associated_item_count":tcx.associated_items(definition).in_definition_order().count()}));
        }
        Ok(json!({"declarations":declarations}))
    }
}
