//! Exact function attributes used by Tree Borrows protected-reference retags.
//! Query the frame instance's DefId, rather than inferring from function names.
use super::*;
#[derive(serde::Serialize)]
pub(super) struct Query {
    definition: u64,
    rustc_no_writable: bool,
}

pub(super) fn export(tcx: TyCtxt<'_>, context: &mut ExportContext<'_>) -> Vec<Query> {
    let mut definitions = context
        .instance_ids
        .keys()
        .filter(|instance| !context.metadata_only_instances.contains(instance))
        .map(|instance| instance.def_id())
        .collect::<Vec<_>>();
    definitions.sort_by_key(|definition| (definition.krate.as_u32(), definition.index.as_u32()));
    definitions.dedup();
    definitions
        .into_iter()
        .map(|definition| Query {
            definition: def_json(context, definition),
            rustc_no_writable: rustc_attr_ir::find_attr!(tcx, definition, RustcNoWritable),
        })
        .collect()
}
