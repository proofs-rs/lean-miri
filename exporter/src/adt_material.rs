//! Canonical compiler-owned ADT declaration records, before instantiation.
//! Physical identities and source attributes are retained; no layout, trait,
//! discriminant evaluation or stable-hash result is acquired here.
use rustc_hir::{def::{CtorKind,DefKind},def_id::DefId};
use rustc_middle::ty::{self,TyCtxt};
use serde_json::{json,Value};
fn identity(definition:DefId)->Value {
    json!({"crate":definition.krate.as_u32(),"index":definition.index.as_u32()})
}
fn optional_identity(definition:Option<DefId>)->Value {
    definition.map(|definition|json!({"definition":identity(definition)})).unwrap_or(Value::Null)
}
pub(super) fn declaration<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId)->Result<Option<Value>,String> {
    if !matches!(tcx.def_kind(definition),DefKind::Struct|DefKind::Enum|DefKind::Union) {
        return Ok(None);
    }
    let adt=tcx.adt_def(definition);
    let mut fields=Vec::new();
    let mut variants=Vec::new();
    for (variant_index,variant) in adt.variants().iter_enumerated() {
        variant.has_errors().map_err(|_|"tainted source ADT variant cannot become raw material".to_owned())?;
        let constructor=variant.ctor.map(|(kind,definition)|json!({
            "kind":match kind{CtorKind::Fn=>"function",CtorKind::Const=>"constant"},
            "definition":identity(definition)}));
        let discriminant=match variant.discr {
            ty::VariantDiscr::Relative(distance)=>json!({"kind":"relative","distance":distance}),
            ty::VariantDiscr::Explicit(definition)=>json!({"kind":"explicit","definition":identity(definition)}),
        };
        variants.push(json!({"definition":identity(variant.def_id),"constructor":constructor,
            "name":variant.name.to_string(),"discriminant":discriminant,
            "field_count":variant.fields.len(),"flags_bits":u8::from(variant.is_field_list_non_exhaustive())}));
        for (field_index,field) in variant.fields.iter_enumerated() {
            let visibility=match field.vis {ty::Visibility::Public=>None,ty::Visibility::Restricted(module)=>Some(module.to_def_id())};
            let mutation_restriction=match field.mut_restriction {
                ty::RestrictionKind::Unrestricted=>None,ty::RestrictionKind::Restricted(definition,_)=>Some(definition),
            };
            fields.push(json!({"variant":variant_index.as_usize(),"field":field_index.as_usize(),
                "unsafe":field.safety.is_unsafe(),"field_name":field.name.to_string(),
                "definition":identity(field.did),"visibility":optional_identity(visibility),
                "mutation_restriction":optional_identity(mutation_restriction),"default_value":optional_identity(field.value)}));
        }
    }
    Ok(Some(json!({"representation":super::repr_options_json(&adt.repr()),
        "flags_bits":adt.flags().bits(),"lang_item":tcx.as_lang_item(definition).map(|item|item.name().as_str().to_owned()),
        "nonnull_optimization_guaranteed":rustc_attr_ir::find_attr!(tcx,definition,RustcNonnullOptimizationGuaranteed),
        "variants":variants,"fields":fields})))
}
