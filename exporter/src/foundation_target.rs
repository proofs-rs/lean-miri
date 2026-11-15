//! Finite target source facts shared with the fixed interpreter's metadata bridge.
//!
//! This queries only rustc's parsed target data layout, never a type layout,
//! instance, ABI, or monomorphic query closure. The shared producer retains the
//! pinned parser's private pointer-space inventory and fails on unsupported
//! object-bound widths rather than guessing a host target.
use rustc_middle::ty::TyCtxt;

pub(super) fn export(tcx: TyCtxt<'_>) -> Result<super::producer::TargetDataLayout, String> {
    super::runtime_target_data_layout_json(tcx)
}
