//! Finite existential predicate syntax, not trait selection or vtable answers.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn dynamic_type(&mut self, tcx: TyCtxt<'tcx>, predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
        region: ty::Region<'tcx>) -> Result<Value> {
        let region = self.signature_region(tcx,region)?;
        let predicates = predicates.iter().map(|bound| {
            if !bound.bound_vars().is_empty() { return unsupported("bound existential predicate",bound); }
            Ok(match bound.skip_binder() {
                ty::ExistentialPredicate::Trait(reference) => {
                    let definition = self.definition(tcx,reference.def_id);
                    self.definitions[definition]["trait_is_auto"] = json!(tcx.trait_is_auto(reference.def_id));
                    json!({"kind":"trait","definition":definition,"arguments":self.args(tcx,reference.args)?,"bound_variables":[]})
                },
                ty::ExistentialPredicate::AutoTrait(def) => {
                    let definition = self.definition(tcx,def);
                    self.definitions[definition]["trait_is_auto"] = json!(tcx.trait_is_auto(def));
                    json!({"kind":"auto_trait","definition":definition,"bound_variables":[]})
                },
                ty::ExistentialPredicate::Projection(projection) => {
                    let ty::TermKind::Ty(term) = projection.term.kind()
                        else { return unsupported("existential const projection",projection); };
                    json!({"kind":"projection","definition":self.definition(tcx,projection.def_id),
                        "parent_trait":self.definition(tcx,tcx.parent(projection.def_id)),
                        "arguments":self.args(tcx,projection.args)?,"term":{"kind":"type","type":self.ty(tcx,term)?},"bound_variables":[]})
                },
            })
        }).collect::<Result<Vec<_>>>()?;
        Ok(json!({"kind":"dynamic","region":region,"predicates":predicates}))
    }
}
