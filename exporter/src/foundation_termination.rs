//! Complete finite declaration headers of a demanded termination language trait.
//! No impl selection, normalization, method instance or executable body answers.
use super::*;

fn self_constructor(value: ty::Ty<'_>) -> Value {
    match *value.kind() {
        ty::Tuple(elements) => json!({"kind":"tuple","arity":elements.len()}),
        ty::Adt(def,_) => json!({"kind":"adt","crate_index":def.did().krate.as_u32(),"index":def.did().index.as_u32()}),
        ty::Never => json!({"kind":"never"}),
        // Param/alias roots may overlap unit under substitution/normalization.
        other => json!({"kind":"unknown","diagnostic":format!("{other:?}")}),
    }
}
impl<'tcx> Material<'tcx> {
    pub(super) fn termination_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let Some(definition) = tcx.lang_items().termination() else {return Ok(Value::Null)};
        if !self.def_ids.contains_key(&definition) {return Ok(Value::Null)}
        let trait_definition = self.definition(tcx,definition);
        let declaration = tcx.trait_def(definition);
        let items = tcx.associated_items(definition).in_definition_order().map(|item|json!({
            "definition":self.definition(tcx,item.def_id),"name":item.name().as_str(),
            "kind":match item.kind {ty::AssocKind::Fn{..}=>"method",ty::AssocKind::Type{..}=>"type",ty::AssocKind::Const{..}=>"const"},
            "own_parameter_count":tcx.generics_of(item.def_id).own_params.len(),"has_self":item.is_method()})).collect::<Vec<_>>();
        let generics = tcx.generics_of(definition);
        let super_clauses = tcx.explicit_super_clauses_of(definition).skip_binder().iter().map(|(clause,_)| {
            let bound = clause.kind();
            let value = match bound.skip_binder() {
                ty::ClauseKind::Trait(predicate) => json!({"kind":"trait","definition":self.definition(tcx,predicate.trait_ref.def_id),
                    "polarity":format!("{:?}",predicate.polarity),"argument_count":predicate.trait_ref.args.len(),
                    "self_parameter":match predicate.trait_ref.self_ty().kind() {ty::Param(p)=>Some(p.index),_=>None}}),
                other => json!({"kind":"unsupported","diagnostic":format!("{other:?}")}),
            };
            let mut value=value;
            value["bound_variable_count"]=json!(bound.bound_vars().len());
            value
        }).collect::<Vec<_>>();
        let mut impls = tcx.all_impls(definition).collect::<Vec<_>>();
        impls.sort_by_key(|def|(def.krate.as_u32(),def.index.as_u32()));
        let mut implementations = Vec::new();
        for implementation in impls {
            let header = tcx.impl_trait_header(implementation);
            let reference = header.trait_ref.instantiate_identity().skip_normalization();
            let generics = tcx.generics_of(implementation);
            let clauses = tcx.clauses_of(implementation);
            let methods = tcx.associated_items(implementation).in_definition_order().map(|item|json!({
                "definition":self.definition(tcx,item.def_id),
                "own_parameter_count":tcx.generics_of(item.def_id).own_params.len(),"trait_item":item.trait_item_def_id().map(|def|self.definition(tcx,def)),
                "kind":match item.kind {ty::AssocKind::Fn{..}=>"method",ty::AssocKind::Type{..}=>"type",ty::AssocKind::Const{..}=>"const"}})).collect::<Vec<_>>();
            implementations.push(json!({"definition":self.definition(tcx,implementation),
                "trait_definition":self.definition(tcx,reference.def_id),"argument_count":reference.args.len(),
                "self_constructor":self_constructor(reference.self_ty()),
                "parameter_count":generics.count(),"generic_parent":generics.parent.map(|def|self.definition(tcx,def)),
                "clause_count":clauses.clauses.len(),"clause_parent":clauses.parent.map(|def|self.definition(tcx,def)),
                "polarity":format!("{:?}",header.polarity),"constness":format!("{:?}",header.constness),"final":tcx.defaultness(implementation).is_final(),
                "associated_items":methods}));
        }
        Ok(json!({"definition":trait_definition,"lang_item":"termination",
            "auto":tcx.trait_is_auto(definition),"marker":declaration.is_marker,"coinductive":declaration.is_coinductive,
            "safety":format!("{:?}",declaration.safety),"constness":format!("{:?}",declaration.constness),
            "meta_sized_definition":tcx.lang_items().meta_sized_trait().map(|def|self.definition(tcx,def)),
            "meta_sized_core_source":tcx.lang_items().meta_sized_trait().is_some_and(|def|!def.is_local() && tcx.crate_name(def.krate).as_str()=="core" && !rustc_attr_ir::find_attr!(tcx, crate, NoCore)),
            "parameter_count":generics.count(),"has_self":generics.has_self,"generic_parent":generics.parent.map(|def|self.definition(tcx,def)),
            "super_clauses":super_clauses,"associated_items":items,"complete_impl_headers":true,"implementations":implementations}))
    }
}

// Finite source-template domain, not trait selection: all non-generic unit
// headers retain their method bodies. The complete declaration table above
// remains authoritative; Lean chooses/rejects the requested concrete header.
pub(super) fn unit_methods(tcx: TyCtxt<'_>) -> Vec<DefId> {
    let Some(trait_def) = tcx.lang_items().termination() else {return Vec::new()};
    tcx.all_impls(trait_def).filter(|implementation| {
        let reference = tcx.impl_trait_header(*implementation).trait_ref.instantiate_identity().skip_normalization();
        matches!(reference.self_ty().kind(),ty::Tuple(fields) if fields.is_empty())
            && tcx.generics_of(*implementation).count()==0
    }).flat_map(|implementation|tcx.associated_items(implementation).in_definition_order()
        .filter(|item|matches!(item.kind,ty::AssocKind::Fn {..})).map(|item|item.def_id).collect::<Vec<_>>()).collect()
}
impl<'tcx> Material<'tcx> {
    pub(super) fn termination_templates(&mut self, tcx: TyCtxt<'tcx>, _roots: &[String]) -> Result<Vec<Value>> {
        let Some(trait_def)=tcx.lang_items().termination() else {return Ok(Vec::new())};
        if !self.def_ids.contains_key(&trait_def) {return Ok(Vec::new())}
        unit_methods(tcx).into_iter().map(|definition| {
            if !tcx.is_mir_available(definition) {return unsupported("unit trait method MIR unavailable",definition)}
            self.body(tcx,definition,false)
        }).collect()
    }
}
