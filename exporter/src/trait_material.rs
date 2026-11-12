//! Raw trait declaration/impl-clause material, pinned rustc 8144389c895d.
//! Clause binders and all source ClauseKind variants are retained. This module
//! never calls trait selection, projection normalization or per-type proof queries.
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_middle::ty::inherent::IntoKind;
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
fn alias(value: ty::AliasTermKind<TyCtxt<'_>>) -> (&'static str, DefId) {
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
