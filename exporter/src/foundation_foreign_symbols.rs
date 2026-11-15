//! Finite session target/linkage state. No instance, export winner, static
//! allocation or foreign-call query catalog is constructed here.
use rustc_ast::expand::allocator::AllocatorKind;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

pub(super) fn export(tcx: TyCtxt<'_>) -> Result<Value, String> {
    let kind = |value| match value {
        AllocatorKind::Global => "global", AllocatorKind::Default => "default",
    };
    // v0::mangle_internal_symbol encodes the fixed __rustc namespace and cfg
    // version hash, followed by push_ident(item_name). The empty identifier is
    // exactly "0". Retain that namespace identity, not a list of symbol answers.
    let mut namespace = rustc_symbol_mangling::mangle_internal_symbol(tcx, "");
    if namespace.pop() != Some('0') {
        return Err("foundation: unexpected internal-symbol namespace encoding".into());
    }
    let target = &tcx.sess.target;
    let mut families = target.families.iter().map(|f|f.as_ref().to_owned()).collect::<Vec<_>>();
    families.sort();
    Ok(json!({"os":target.os.desc_symbol().as_str(),"env":target.env.desc_symbol().as_str(),
        "binary_format":target.binary_format.desc_symbol().as_str(),"families":families,
        "internal_symbol_namespace":namespace,
        "allocator_kind":tcx.allocator_kind(()).map(kind),
        "alloc_error_handler_kind":tcx.alloc_error_handler_kind(()).map(kind)}))
}
