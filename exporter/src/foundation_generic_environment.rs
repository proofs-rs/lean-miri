//! Ordered lexical generic declaration layers. No inherited arguments or
//! predicate answers are supplied; Lean checks/concatenates these source layers.
use super::*;
impl<'tcx> Material<'tcx> {
    fn own_environment_clauses(&mut self, tcx: TyCtxt<'tcx>, def: DefId) -> Result<Vec<Value>> {
        tcx.clauses_of(def).clauses.iter().map(|(predicate,_)| {
            let bound = predicate.kind();
            if !bound.bound_vars().is_empty() { return unsupported("bound predicate",predicate); }
            Ok(match bound.skip_binder() {
                ty::ClauseKind::Trait(reference) if reference.polarity == ty::ClausePolarity::Positive => {
                    let trait_def = reference.trait_ref.def_id;
                    let definition = self.definition(tcx,trait_def);
                    if trait_def.is_local() && self.definitions[definition].get("local_trait").is_none() {
                        self.definitions[definition]["local_trait"] = super::super::foundation_traits::capture(tcx,trait_def)?;
                    }
                    let role = if tcx.is_lang_item(trait_def,rustc_attr_ir::LangItem::Sized) {Some("sized")}
                        else if tcx.is_lang_item(trait_def,rustc_attr_ir::LangItem::Copy) {Some("copy")}
                        else if tcx.is_lang_item(trait_def,rustc_attr_ir::LangItem::MetaSized) {Some("meta_sized")}
                        else {None};
                    json!({"kind":"trait","definition":definition,"lang_item":role,"pinned_core_builtin":role.is_some() && !trait_def.is_local() && tcx.crate_name(trait_def.krate).as_str()=="core" && !rustc_attr_ir::find_attr!(tcx, crate, NoCore),"arguments":self.args(tcx,reference.trait_ref.args)?})
                },
                ty::ClauseKind::Projection(projection) => self.projection_clause(tcx,projection)?,
                ty::ClauseKind::TypeOutlives(outlives) =>
                    json!({"kind":"type_outlives","type":self.ty(tcx,outlives.0)?,
                        "region":self.signature_region(tcx,outlives.1)?}),
                ty::ClauseKind::RegionOutlives(outlives) => json!({"kind":"region_outlives",
                    "longer":self.signature_region(tcx,outlives.0)?,"shorter":self.signature_region(tcx,outlives.1)?}),
                ty::ClauseKind::ConstArgHasType(value,ty) => json!({"kind":"const_has_type","value":self.constant(tcx,value)?,"type":self.ty(tcx,ty)?}),
                other => return unsupported("predicate",other),
            })
        }).collect()
    }

    pub(super) fn generic_environment(&mut self, tcx: TyCtxt<'tcx>, definition: DefId) -> Result<Value> {
        let mut owners = Vec::new();
        let mut current = Some(definition);
        while let Some(owner) = current {
            if owners.contains(&owner) || owners.len() >= 256 { return unsupported("generic parent source cycle/depth",owner); }
            owners.push(owner);
            current = tcx.generics_of(owner).parent;
        }
        owners.reverse();
        let mut layers = Vec::new();
        for owner in owners {
            let generics = tcx.generics_of(owner);
            let predicates = tcx.clauses_of(owner);
            if predicates.parent != generics.parent { return unsupported("generic/predicate parent source mismatch",owner); }
            let owner_id = self.definition(tcx,owner);
            let parent = generics.parent.map(|parent|self.definition(tcx,parent));
            let self_type = if matches!(tcx.def_kind(owner),rustc_hir::def::DefKind::Impl {..}) {
                Some(self.ty(tcx,tcx.type_of(owner).instantiate_identity().skip_normalization())?)
            } else {None};
            self.definitions[owner_id]["generic_declaration"] = json!({"parent":parent,
                "parent_count":generics.parent_count,"own_parameter_count":generics.own_params.len(),"self_type":self_type,"has_self":generics.has_self});
            let parameters = generics.own_params.iter().map(|parameter| {
                let value = self.generic_parameter(tcx,parameter)?;
                let id = self.definition(tcx,parameter.def_id);
                self.definitions[id]["generic_parameter"] = json!({"owner":owner_id,"index":parameter.index});
                Ok(value)
            }).collect::<Result<Vec<_>>>()?;
            layers.push(json!({"owner":owner_id,"parent":parent,"parent_count":generics.parent_count,
                "parameters":parameters,"clauses":self.own_environment_clauses(tcx,owner)?,"self_type":self_type,"has_self":generics.has_self}));
        }
        Ok(json!({"owner":self.definition(tcx,definition),"layers":layers}))
    }
}
