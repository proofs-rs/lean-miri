//! Raw DefKey chain and generic declaration headers, never printer query answers.
use rustc_hir::{def::DefKind, definitions::DefPathData, def_id::DefId};
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json,Value};
pub(crate) fn material(tcx:TyCtxt<'_>, definition:DefId)->Option<Value> {
    if !matches!(tcx.def_kind(definition),DefKind::Struct|DefKind::Enum|DefKind::Union|DefKind::Fn|DefKind::AssocFn) {
        return None;
    }
    let mut current=definition;
    let mut components=Vec::new();
    loop {
        let key=tcx.def_key(current);
        let (kind,name)=match key.disambiguated_data.data {
            DefPathData::CrateRoot=>("crate_root",Some(tcx.crate_name(current.krate).to_string())),
            DefPathData::TypeNs(name)=>("type",Some(name.to_string())),
            DefPathData::ValueNs(name)=>("value",Some(name.to_string())),
            DefPathData::Impl=>("impl",None),
            DefPathData::ForeignMod=>("foreign_module",None),
            DefPathData::Ctor=>("constructor",None),
            _=>("unsupported",None),
        };
        components.push(json!({"kind":kind,"name":name,"disambiguator":key.disambiguated_data.disambiguator}));
        match key.parent {Some(index)=>current=DefId{krate:current.krate,index},None=>break}
    }
    components.reverse();
    let generics=tcx.generics_of(definition);
    let defaults=generics.own_params.iter().map(|parameter| match parameter.kind {
        ty::GenericParamDefKind::Lifetime=>false,
        ty::GenericParamDefKind::Type{has_default,..}=>has_default,
        ty::GenericParamDefKind::Const{has_default,..}=>has_default,
    }).collect::<Vec<_>>();
    Some(json!({"components":components,"parent_parameter_count":generics.parent_count,"parameter_defaults":defaults}))
}
