//! Raw DefKey chain and generic declaration headers, never printer query answers.
use rustc_hir::{def::DefKind, definitions::DefPathData, def_id::DefId};
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json,Value};
pub(crate) fn material(tcx:TyCtxt<'_>, definition:DefId)->Option<Value> {
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
            DefPathData::Use=>("use",None),
            DefPathData::GlobalAsm=>("global_asm",None),
            DefPathData::MacroNs(name)=>("macro",Some(name.to_string())),
            DefPathData::LifetimeNs(name)=>("lifetime",Some(name.to_string())),
            DefPathData::Closure=>("closure",None),
            DefPathData::TestBinderConstraints=>("test_binder_constraints",None),
            DefPathData::AnonConst=>("anonymous_constant",None),
            DefPathData::OpaqueTy=>("opaque_type",None),
            DefPathData::OpaqueLifetime(name)=>("opaque_lifetime",Some(name.to_string())),
            DefPathData::AnonAssocTy(name)=>("anonymous_associated_type",Some(name.to_string())),
            DefPathData::SyntheticCoroutineBody=>("synthetic_coroutine_body",None),
            DefPathData::NestedStatic=>("nested_static",None),
        };
        components.push(json!({"kind":kind,"name":name,"disambiguator":key.disambiguated_data.disambiguator}));
        match key.parent {Some(index)=>current=DefId{krate:current.krate,index},None=>break}
    }
    components.reverse();
    // A path is raw metadata for every definition, including lifetime and
    // type parameters. Only `has_generics` definitions admit this query.
    // Unsupported raw defaults leave the declaration header unavailable;
    // they never erase the physical path or masquerade as absent defaults.
    let generic_header = tcx.def_kind(definition).has_generics().then(|| {
        let generics = tcx.generics_of(definition);
        let parameters = (0..generics.count()).map(|index|
            match generics.param_at(index,tcx).kind {
                ty::GenericParamDefKind::Lifetime => "region",
                ty::GenericParamDefKind::Type { .. } => "type",
                ty::GenericParamDefKind::Const { .. } => "constant",
            }).collect::<Vec<_>>();
        let defaults = generics.own_params.iter().map(|parameter| {
            parameter.default_value(tcx).map(|default| {
                crate::generic_material::argument(tcx, default.skip_binder())
                    .and_then(|tree| serde_json::from_str::<Value>(&tree).map_err(|error|error.to_string()))
            }).transpose()
        }).collect::<Result<Vec<_>,String>>()?;
        Ok::<_,String>(json!({"parent_parameter_count":generics.parent_count,
            "parameters":parameters,"default_expressions":defaults}))
    }).and_then(Result::ok);
    let function_header_safety = definition.as_local().and_then(|local| {
        if !matches!(tcx.def_kind(definition),DefKind::Fn|DefKind::AssocFn) {return None;}
        tcx.hir_node_by_def_id(local).fn_sig().map(|signature| match signature.header.safety {
            rustc_hir::HeaderSafety::Normal(rustc_hir::Safety::Safe)=>"normal_safe",
            rustc_hir::HeaderSafety::Normal(rustc_hir::Safety::Unsafe)=>"normal_unsafe",
            rustc_hir::HeaderSafety::SafeTargetFeatures=>"safe_target_features",
        })
    });
    Some(json!({"stable_crate_id":tcx.stable_crate_id(definition.krate).as_u64(),
        "function_header_safety":function_header_safety,"components":components,
        "generic_header":generic_header}))
}
