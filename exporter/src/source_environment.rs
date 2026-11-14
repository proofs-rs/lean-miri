//! Raw source generic-scope predicates. No normalization or trait selection.
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};

/// Call only for demanded generic definitions and their generic parent scopes.
/// Retaining a parent scope does not demand its members' signatures or bodies.
pub(super) fn declaration<'tcx>(tcx: TyCtxt<'tcx>, definition: DefId,
    mut encode_clause: impl FnMut(ty::Clause<'tcx>) -> Result<Value, String>)
    -> Result<Value, String>
{
    let generics = tcx.generics_of(definition);
    let parameters = (0..generics.count()).map(|index|
        match generics.param_at(index, tcx).kind {
            ty::GenericParamDefKind::Lifetime => "region",
            ty::GenericParamDefKind::Type { .. } => "type",
            ty::GenericParamDefKind::Const { .. } => "constant",
        }).collect::<Vec<_>>();
    let generic_parent = generics.parent.map(|parent| json!({
        "definition": {"crate":parent.krate.as_u32(),"index":parent.index.as_u32()},
        "parameter_count":generics.parent_count,
    }));
    let explicit = tcx.explicit_clauses_of(definition);
    let predicate_parent = explicit.parent.map(|parent| json!({
        "definition": {"crate":parent.krate.as_u32(),"index":parent.index.as_u32()},
        "parameter_count":tcx.generics_of(parent).count(),
    }));
    let own_predicates = explicit.clauses.iter()
        .map(|(clause, _)| encode_clause(*clause)).collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"parameters":parameters,"predicate_parent":predicate_parent,
        "generic_parent":generic_parent,"is_trait":tcx.is_trait(definition),
        "own_predicates":own_predicates}))
}
