//! Exact intrinsics.rs::write_type_id compiler leaves (lines 91–98).
//! A compiler hash is evidence, never a hash reconstructed from type spelling.
use super::*;
pub(super) fn type_id_hash<'tcx>(tcx:TyCtxt<'tcx>,input:ty::Ty<'tcx>)->Value {
    if input.has_non_region_param() || input.has_escaping_bound_vars() || input.has_infer()
        || input.has_placeholders() || input.references_error() {
        return unavailable_compiler_fact("TypeId hash requires complete monomorphic type identity");
    }
    if input.has_erasable_regions(){
        return unavailable_compiler_fact("write_type_id source requires erasable regions removed");
    }
    compiler_fact(json!(tcx.type_id_hash(input).as_u128().to_string()))
}
