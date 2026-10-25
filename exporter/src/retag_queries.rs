//! Exact function attributes used by Tree Borrows protected-reference retags.
//! Query the frame instance's DefId, rather than inferring from function names.
use super::*;

pub(super) fn export(tcx: TyCtxt<'_>, context: &ExportContext<'_>) -> Value {
    let mut definitions = context.instance_ids.keys()
        .map(|instance| instance.def_id()).collect::<Vec<_>>();
    definitions.sort_by_key(|definition| (definition.krate.as_u32(), definition.index.as_u32()));
    definitions.dedup();
    Value::Array(definitions.into_iter().map(|definition| json!({
        "definition": def_json(definition),
        "status": "supported",
        "rustc_no_writable": rustc_attr_ir::find_attr!(tcx, definition, RustcNoWritable),
    })).collect())
}
