//! Canonical source ADT attributes. No instantiated type or trait query result.
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::ty::TyCtxt;
use serde_json::{json,Value};
pub(super) fn declaration<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId)->Result<Option<Value>,String> {
    let kind=match tcx.def_kind(definition) {
        DefKind::Struct=>"struct",DefKind::Enum=>"enum",DefKind::Union=>"union",_=>return Ok(None),
    };
    let adt=tcx.adt_def(definition);
    let mut fields=Vec::new();
    for (variant_index,variant) in adt.variants().iter_enumerated() {
        for (field_index,field) in variant.fields.iter_enumerated() {
            fields.push(json!({"variant":variant_index.as_usize(),"field":field_index.as_usize(),"unsafe":field.safety.is_unsafe(),"field_name":field.name.to_string()}));
        }
    }
    Ok(Some(json!({"representation":super::repr_options_json(&adt.repr()),"kind":kind,"lang_item":tcx.as_lang_item(definition).map(|item|item.name().as_str().to_owned()),"variant_count":adt.variants().len(),"variant_names":adt.variants().iter().map(|variant|variant.name.to_string()).collect::<Vec<_>>(),"fields":fields})))
}
