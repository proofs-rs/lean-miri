//! Raw trait declaration/impl-clause material, pinned rustc 8144389c895d.
//! Clause binders and all source ClauseKind variants are retained. This module
//! never calls trait selection, projection normalization or per-type proof queries.
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};

pub(super) fn identity(definition: DefId) -> Value {
    json!({"crate":definition.krate.as_u32(),"index":definition.index.as_u32()})
}
fn tree(value: Result<String, String>) -> Result<Value, String> {
    serde_json::from_str(&value?).map_err(|error| format!("invalid raw generic tree: {error}"))
}
pub(super) fn trait_ref<'tcx>(tcx: TyCtxt<'tcx>, value: ty::TraitRef<'tcx>) -> Result<Value, String> {
    let arguments = value.args.iter().map(|arg| tree(super::generic_material::argument(tcx, arg)))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"definition":identity(value.def_id),"arguments":arguments}))
}
fn term<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Term<'tcx>) -> Result<Value, String> {
    tree(match value.kind() {
        ty::TermKind::Ty(value) => super::generic_material::type_tree(tcx, value),
        ty::TermKind::Const(value) => super::generic_material::constant_tree(tcx, value),
    })
}
fn alias(value: ty::AliasTermKind<'_>) -> (&'static str, DefId) {
    match value {
        ty::AliasTermKind::ProjectionTy { def_id } => ("projection_type", def_id),
        ty::AliasTermKind::InherentTy { def_id } => ("inherent_type", def_id),
        ty::AliasTermKind::OpaqueTy { def_id } => ("opaque_type", def_id),
        ty::AliasTermKind::FreeTy { def_id } => ("free_type", def_id),
        ty::AliasTermKind::AnonConst { def_id } => ("anonymous_const", def_id),
        ty::AliasTermKind::ProjectionConst { def_id } => ("projection_const", def_id),
        ty::AliasTermKind::FreeConst { def_id } => ("free_const", def_id),
        ty::AliasTermKind::InherentConstSelf { def_id } => ("inherent_const_self", def_id),
        ty::AliasTermKind::InherentConstImpl { def_id } => ("inherent_const_impl", def_id),
    }
}

pub(super) fn clause<'tcx>(tcx: TyCtxt<'tcx>, value: ty::Clause<'tcx>) -> Result<Value, String> {
    let bound = value.kind();
    let variables = bound.bound_vars().iter().map(|variable| {
        serde_json::from_str::<Value>(&super::generic_material::bound_variable(variable))
            .map_err(|error| format!("invalid raw clause binder: {error}"))
    }).collect::<Result<Vec<_>, _>>()?;
    let predicate = match bound.skip_binder() {
        ty::ClauseKind::Trait(value) => json!({"kind":"trait",
            "polarity": match value.polarity {ty::ClausePolarity::Positive=>"positive",ty::ClausePolarity::Negative=>"negative"},
            "trait_ref":trait_ref(tcx,value.trait_ref)?}),
        ty::ClauseKind::RegionOutlives(value) => json!({"kind":"region_outlives",
            "longer":tree(super::generic_material::region_tree(value.0))?,
            "shorter":tree(super::generic_material::region_tree(value.1))?}),
        ty::ClauseKind::TypeOutlives(value) => json!({"kind":"type_outlives",
            "type":tree(super::generic_material::type_tree(tcx,value.0))?,
            "region":tree(super::generic_material::region_tree(value.1))?}),
        ty::ClauseKind::Projection(value) => {
            let (kind, definition) = alias(value.projection_term.kind);
            let arguments = value.projection_term.args.iter()
                .map(|arg|tree(super::generic_material::argument(tcx,arg))).collect::<Result<Vec<_>,_>>()?;
            json!({"kind":"projection","alias_kind":kind,"associated":identity(definition),
                "arguments":arguments,"expected":term(tcx,value.term)?})
        },
        ty::ClauseKind::ConstArgHasType(value, ty) => json!({"kind":"const_has_type",
            "value":tree(super::generic_material::constant_tree(tcx,value))?,
            "type":tree(super::generic_material::type_tree(tcx,ty))?}),
        ty::ClauseKind::WellFormed(value) => json!({"kind":"well_formed","value":term(tcx,value)?}),
        ty::ClauseKind::ConstEvaluatable(value) => json!({"kind":"const_evaluatable",
            "value":tree(super::generic_material::constant_tree(tcx,value))?}),
        ty::ClauseKind::HostEffect(value) => json!({"kind":"host_effect",
            "requires_const":matches!(value.constness,ty::BoundConstness::Const),
            "trait_ref":trait_ref(tcx,value.trait_ref)?}),
        ty::ClauseKind::UnstableFeature(feature) => json!({"kind":"unstable_feature","feature":feature.as_str()}),
    };
    Ok(json!({"variables":variables,"predicate":predicate}))
}

fn parameters(tcx: TyCtxt<'_>, definition: DefId) -> Vec<&'static str> {
    let generics = tcx.generics_of(definition);
    (0..generics.count()).map(|index| match generics.param_at(index, tcx).kind {
        ty::GenericParamDefKind::Lifetime => "region",
        ty::GenericParamDefKind::Type { .. } => "type",
        ty::GenericParamDefKind::Const { .. } => "constant",
    }).collect()
}
fn implementation(tcx: TyCtxt<'_>, definition: DefId) -> Result<Value, String> {
    let head = tcx.impl_trait_ref(definition).skip_binder();
    let mut values = Vec::new();
    let mut methods = Vec::new();
    let mut constants = Vec::new();
    for item in tcx.associated_items(definition).in_definition_order() {
        let Some(trait_item) = item.trait_item_def_id() else {
            return Err("trait impl associated item has no trait declaration identity".into());
        };
        let final_item = item.defaultness(tcx).is_final();
        match item.kind {
            ty::AssocKind::Type { .. } => values.push(json!({
                "trait_associated_definition":identity(trait_item),
                "implementation_definition":identity(item.def_id),
                "has_value":item.defaultness(tcx).has_value(),
                "requires_hidden_type_inference":item.is_impl_trait_in_trait(),
            })),
            ty::AssocKind::Fn { .. } => methods.push(json!({
                "trait_associated_definition":identity(trait_item),
                "implementation_definition":identity(item.def_id),"is_final":final_item,
            })),
            ty::AssocKind::Const { .. } => constants.push(json!({
                "trait_associated_definition":identity(trait_item),
                "implementation_definition":identity(item.def_id),"is_final":final_item,
            })),
        }
    }
    let polarity = match tcx.impl_polarity(definition) {
        ty::ImplPolarity::Positive => "positive", ty::ImplPolarity::Negative => "negative",
    };
    Ok(json!({"definition":identity(definition),"parameters":parameters(tcx,definition),
        "trait_ref":trait_ref(tcx,head)?,"polarity":polarity,
        "is_default":!tcx.defaultness(definition).is_final(),
        "associated_values":values,
        "methods":methods,"constants":constants}))
}
fn declaration(tcx: TyCtxt<'_>, definition: DefId, constructors: &std::collections::HashSet<DefId>) -> Result<Value, String> {
    use rustc_hir::def::DefKind;
    let alias = tcx.def_kind(definition) == DefKind::TraitAlias;
    if !alias && tcx.def_kind(definition) != DefKind::Trait {
        return Err("raw trait catalog key is not a trait or trait alias".into());
    }
    let data = if alias { None } else { Some(tcx.trait_def(definition)) };
    let mut implementations = if alias { vec![] } else { tcx.all_impls(definition).collect::<Vec<_>>() };
    // This is a syntactic source-head filter, not candidate selection. An
    // impl with a concrete root Self ADT cannot match any ground query in a
    // closed constructor universe that does not contain that ADT. Blanket,
    // alias and non-ADT heads remain conservatively retained.
    implementations.retain(|id| match tcx.impl_trait_ref(*id).skip_binder().self_ty().kind() {
        ty::Adt(adt, _) => constructors.contains(&adt.did()),
        _ => true,
    });
    implementations.sort_by_key(|id| (id.krate.as_u32(),id.index.as_u32()));
    let implementations = implementations.into_iter().map(|id| implementation(tcx,id))
        .collect::<Result<Vec<_>,_>>()?;
    let mut members = Vec::new();
    if !alias {
        for item in tcx.associated_items(definition).in_definition_order() {
            let kind = match item.kind {ty::AssocKind::Type{..}=>"type",ty::AssocKind::Fn{..}=>"function",ty::AssocKind::Const{..}=>"constant"};
            members.push(json!({"definition":identity(item.def_id),"kind":kind,
                "has_value":item.defaultness(tcx).has_value(),"is_final":item.defaultness(tcx).is_final(),
                "is_method":item.is_method(),"is_impl_trait_in_trait":item.is_impl_trait_in_trait()}));
        }
    }
    let super_predicates = tcx.explicit_super_clauses_of(definition).skip_binder().iter()
        .map(|(value,_)|clause(tcx,*value)).collect::<Result<Vec<_>,_>>()?;
    Ok(json!({"definition":identity(definition),"parameters":parameters(tcx,definition),
        "is_alias":alias,"is_auto":data.is_some_and(|data|data.has_auto_impl),
        "is_unsafe":data.is_some_and(|data|data.safety.is_unsafe()),
        "is_coinductive":data.is_some_and(|data|data.is_coinductive),
        "is_marker":data.is_some_and(|data|data.is_marker),
        "lang_item":tcx.as_lang_item(definition).map(|item|item.name().as_str().to_string()),
        "super_predicates":super_predicates,"implementations":implementations,"members":members}))
}

#[derive(Default)]
pub(super) struct State {
    pending: std::collections::BTreeMap<(u32,u32),DefId>,
    emitted: std::collections::BTreeMap<(u32,u32), Value>,
    constructors: std::collections::HashSet<DefId>,
}
impl State {
    pub(super) fn seed(tcx: TyCtxt<'_>) -> Self {
        let mut state = Self::default();
        for language_item in [rustc_attr_ir::LangItem::Freeze,rustc_attr_ir::LangItem::Unpin,
            rustc_attr_ir::LangItem::UnsafeUnpin,rustc_attr_ir::LangItem::Sized,
            rustc_attr_ir::LangItem::MetaSized,rustc_attr_ir::LangItem::Unsize,
            rustc_attr_ir::LangItem::DispatchFromDyn,rustc_attr_ir::LangItem::Copy,rustc_attr_ir::LangItem::Clone] {
            if let Some(definition) = tcx.lang_items().get(language_item) { state.pending.insert((definition.krate.as_u32(),definition.index.as_u32()),definition); }
        }
        state
    }
    /// Grow only from retained source expressions, never catalog identity
    /// headers. Revisit prior declarations when a new constructible ADT enters
    /// the domain, so filtering is a monotone declaration dependency closure.
    pub(super) fn update_constructors(&mut self, tcx: TyCtxt<'_>, demanded: &std::collections::HashSet<DefId>) {
        use rustc_hir::def::DefKind;
        let mut changed = false;
        for definition in demanded {
            if matches!(tcx.def_kind(*definition), DefKind::Struct | DefKind::Enum | DefKind::Union) {
                changed |= self.constructors.insert(*definition);
            }
        }
        if changed {
            for key in self.emitted.keys() {
                self.pending.insert(*key, DefId {
                    krate: rustc_hir::def_id::CrateNum::from_u32(key.0),
                    index: rustc_hir::def_id::DefIndex::from_u32(key.1),
                });
            }
            self.emitted.clear();
        }
    }
    pub(super) fn register_definition(&mut self, tcx: TyCtxt<'_>, definition: DefId) -> Result<(), String> {
        use rustc_hir::def::DefKind;
        let trait_definition = match tcx.def_kind(definition) {
            DefKind::Trait | DefKind::TraitAlias => Some(definition),
            DefKind::AssocTy | DefKind::AssocFn | DefKind::AssocConst => {
                let item = tcx.associated_item(definition);
                match item.container {
                    ty::AssocContainer::Trait => Some(item.container_id(tcx)),
                    ty::AssocContainer::TraitImpl(Ok(trait_item)) => Some(tcx.parent(trait_item)),
                    ty::AssocContainer::TraitImpl(Err(_)) => return Err("associated trait identity unresolved".into()),
                    ty::AssocContainer::InherentImpl => None,
                }
            },
            _ => None,
        };
        if let Some(definition) = trait_definition {
            let key = (definition.krate.as_u32(),definition.index.as_u32());
            if !self.emitted.contains_key(&key) { self.pending.insert(key,definition); }
        }
        Ok(())
    }
    pub(super) fn discover(&mut self, tcx: TyCtxt<'_>) -> Result<Vec<DefId>, String> {
        let mut references = Vec::new();
        while let Some((key,definition)) = self.pending.pop_first() {
            if self.emitted.contains_key(&key) { continue; }
            let source = declaration(tcx, definition, &self.constructors)?;
            let mut discovered = Vec::new();
            super::generic_definition_references(&source, &mut discovered)?;
            // Mark first so a trait's own declarations cannot reschedule it.
            self.emitted.insert(key, source);
            for reference in &discovered { self.register_definition(tcx, *reference)?; }
            references.extend(discovered);
        }
        Ok(references)
    }
    /// Demand raw source signatures and predicate scopes for retained trait
    /// methods. These declarations drive dyn eligibility, not selected-method
    /// or compiler-computed vtable-entry answers. Associated RHS demand remains
    /// tied to associated declarations occurring in source expressions.
    pub(super) fn rhs_demands(&self, tcx: TyCtxt<'_>, demanded: &std::collections::HashSet<DefId>, scopes: &mut Vec<DefId>) -> Result<Vec<DefId>, String> {
        let mut result = Vec::new();
        for source in self.emitted.values() {
            let trait_definition = read_identity(&source["definition"])?;
            if !source["is_alias"].as_bool().unwrap_or(false) {
                for item in tcx.associated_items(trait_definition).in_definition_order() {
                    if item.is_fn() && !item.defaultness(tcx).is_final() {
                        result.push(item.def_id);
                        scopes.push(item.def_id);
                    }
                }
            }
            // These are the retained source expressions needed for matching
            // and obligations. Member header identities are deliberately absent.
            super::generic_definition_references(&source["super_predicates"], &mut result)?;
            for implementation in source["implementations"].as_array().into_iter().flatten() {
                super::generic_definition_references(&implementation["trait_ref"], &mut result)?;
                let definition = read_identity(&implementation["definition"])?;
                // Scope declarations carry obligations, not method signatures.
                scopes.push(definition);
                for item in tcx.associated_items(definition).in_definition_order() {
                    if matches!(item.kind, ty::AssocKind::Type { .. })
                        && item.trait_item_def_id().is_some_and(|parent| demanded.contains(&parent)) {
                        result.push(item.def_id);
                    }
                }
            }
        }
        Ok(result)
    }
    pub(super) fn finish(self, _tcx: TyCtxt<'_>, demanded: &std::collections::HashSet<DefId>) -> Result<Value, String> {
        let mut constructors = self.constructors.into_iter().collect::<Vec<_>>();
        constructors.sort_by_key(|id| (id.krate.as_u32(), id.index.as_u32()));
        let mut traits = self.emitted.into_values().collect::<Vec<_>>();
        for source in &mut traits {
            for implementation in source["implementations"].as_array_mut().into_iter().flatten() {
                for value in implementation["associated_values"].as_array_mut().into_iter().flatten() {
                    let retained = demanded.contains(&read_identity(&value["implementation_definition"])?);
                    value["material_retained"] = json!(retained);
                }
            }
        }
        Ok(json!({"traits":traits,"constructor_scope":{
            "kind":"closed_source_constructors",
            "constructors":constructors.into_iter().map(identity).collect::<Vec<_>>()
        }}))
    }
}

// Internal JSON is produced solely by identity() above, before transport.
fn read_identity(value: &Value) -> Result<DefId, String> {
    let component = |key: &str| value[key].as_u64().and_then(|n| u32::try_from(n).ok())
        .ok_or_else(|| format!("internal raw trait {key} identity absent/invalid"));
    Ok(DefId { krate: rustc_hir::def_id::CrateNum::from_u32(component("crate")?),
        index: rustc_hir::def_id::DefIndex::from_u32(component("index")?) })
}
