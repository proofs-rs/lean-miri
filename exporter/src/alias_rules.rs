//! Source declaration RHS and own-clause material for alias normalization.
//! No instantiated projection result, impl selection or specialization graph is
//! captured here. The caller supplies the shared raw Clause encoder, preserving
//! binders and predicate variants instead of dropping unsupported conditions.
use rustc_hir::def::{DefKind};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};

fn identity(definition: DefId) -> Value {
    json!({"crate":definition.krate.as_u32(),"index":definition.index.as_u32()})
}

/// The absence of an associated default is declaration material, not a reason to
/// call `type_of` on an abstract item. Impl RHS and explicit trait defaults use
/// their original EarlyBinder expression and complete parameter declaration.
pub(super) fn declaration<'tcx>(
    tcx: TyCtxt<'tcx>,
    definition: DefId,
    mut encode_clause: impl FnMut(ty::Clause<'tcx>) -> Result<Value, String>,
) -> Result<Option<Value>, String> {
    let kind = tcx.def_kind(definition);
    if !matches!(kind, DefKind::TyAlias | DefKind::AssocTy) {
        return Ok(None);
    }
    let mut source = serde_json::Map::new();
    source.insert("definition".into(), identity(definition));
    let has_value = if kind == DefKind::AssocTy {
        let item = tcx.associated_item(definition);
        // Hidden RPITIT values require the inference/opaque constraint port;
        // exporting type_of here would disguise a solver result as source.
        if item.is_impl_trait_in_trait() { return Ok(None); }
        let parent = item.container_id(tcx);
        let container = match item.container {
            ty::AssocContainer::Trait => "trait",
            ty::AssocContainer::InherentImpl => "inherent_impl",
            ty::AssocContainer::TraitImpl(Ok(trait_item)) => {
                source.insert("trait_item".into(), identity(trait_item));
                "trait_impl"
            }
            ty::AssocContainer::TraitImpl(Err(_)) => {
                return Err("associated type has an unresolved trait declaration".into());
            }
        };
        source.insert("kind".into(), json!("associated"));
        source.insert("container".into(), json!(container));
        source.insert("parent".into(), identity(parent));
        source.insert("parent_parameter_count".into(), json!(tcx.generics_of(parent).count()));
        let defaultness = item.defaultness(tcx);
        source.insert("is_final".into(), json!(defaultness.is_final()));
        defaultness.has_value()
    } else {
        source.insert("kind".into(), json!("free"));
        source.insert("is_checked".into(), json!(tcx.type_alias_is_checked(definition)));
        true
    };
    source.insert("has_value".into(), json!(has_value));
    // The RHS is shared through Definition.generic_template, captured once by
    // generic_material::definition_template under the same has_value guard.
    // Do not duplicate instantiated or source RHS trees in per-alias records.
    let clauses = tcx.explicit_clauses_of(definition).clauses.iter()
        .map(|(clause, _span)| encode_clause(*clause))
        .collect::<Result<Vec<_>, _>>()?;
    source.insert("own_predicates".into(), json!(clauses));
    Ok(Some(Value::Object(source)))
}
