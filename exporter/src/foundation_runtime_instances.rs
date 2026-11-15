//! Finite definition attributes and crate identities, never monomorphic instance
//! answers. The consumer constructs supported RuntimeInstance records on demand.
use rustc_hir::def_id::{DefId, LOCAL_CRATE, CRATE_DEF_ID};
use rustc_middle::ty::TyCtxt;
use serde_json::{Value, json};

pub(super) fn item(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let attrs = tcx.codegen_fn_attrs(def);
    json!({
        "is_local_root":def.is_local() && tcx.parent(def) == CRATE_DEF_ID.to_def_id(),
        "item_name":tcx.opt_item_name(def).map(|s|s.as_str().to_owned()),
        "inline":match attrs.inline {
            rustc_attr_ir::InlineAttr::Never=>"never",
            rustc_attr_ir::InlineAttr::None=>"none",
            rustc_attr_ir::InlineAttr::Hint=>"hint",
            rustc_attr_ir::InlineAttr::Always=>"always",
            _=>"unsupported",
        },
        "target_features":attrs.target_features.iter().map(|feature|json!({"name":feature.name.as_str(),"kind":format!("{:?}",feature.kind)})).collect::<Vec<_>>(),
        "rustc_intrinsic":rustc_attr_ir::find_attr!(tcx, def, RustcIntrinsic),
        "codegen_symbol_name":attrs.symbol_name.map(|s|s.as_str().to_owned()),
    })
}

pub(super) fn frames(tcx: TyCtxt<'_>) -> Value {
    let mut crates = tcx.crates(()).iter().copied().collect::<Vec<_>>();
    crates.push(LOCAL_CRATE);
    crates.sort_by_key(|krate| krate.as_u32());
    crates.dedup();
    json!({"local_crate":LOCAL_CRATE.as_u32(),"crates":crates.into_iter()
        .map(|krate|json!({"crate":krate.as_u32(),"name":tcx.crate_name(krate).as_str()}))
        .collect::<Vec<_>>()})
}
