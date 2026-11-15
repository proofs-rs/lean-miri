//! Generic projection-equality declarations; no normalization/selection answer.
use super::*;
impl<'tcx> Material<'tcx> {
    pub(super) fn projection_clause(&mut self, tcx: TyCtxt<'tcx>, projection: ty::ProjectionClause<'tcx>) -> Result<Value> {
        let ty::TermKind::Ty(term) = projection.term.kind()
            else { return unsupported("const projection clause",projection); };
        let definition = projection.def_id();
        if !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::AssocTy) {
            return unsupported("projection clause associated type",definition);
        }
        let parent = tcx.parent(definition);
        if !matches!(tcx.def_kind(parent),rustc_hir::def::DefKind::Trait) {
            return unsupported("projection clause parent trait",parent);
        }
        let definition_id = self.definition(tcx,definition);
        let parent_id = self.definition(tcx,parent);
        let generics = tcx.generics_of(definition);
        self.definitions[definition_id]["associated_type"] = json!({"parent_trait":parent_id,
            "name":tcx.item_name(definition).as_str(),"parent_count":generics.parent_count,
            "own_parameter_count":generics.own_params.len()});
        Ok(json!({"kind":"projection","definition":definition_id,
            "parent_trait":parent_id,"arguments":self.args(tcx,projection.projection_term.args)?,
            "term":{"kind":"type","type":self.ty(tcx,term)?},"bound_variables":[]}))
    }
}
