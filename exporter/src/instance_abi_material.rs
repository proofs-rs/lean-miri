//! Syntactic admission for the raw Lean Item FnAbi provider. This reads the
//! declaration signature and raw codegen flags, never layout_of or FnAbi.
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};

pub(super) fn signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>,
    extra: &'tcx ty::List<ty::Ty<'tcx>>) -> Option<ty::FnSig<'tcx>> {
    use rustc_abi::ExternAbi as A;
    use rustc_hir::def::DefKind as D;
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
    let ty::InstanceKind::Item(definition) = instance.def else { return None };
    if tcx.sess.target.arch != rustc_target::spec::Arch::X86_64 ||
        tcx.sess.target.pointer_width != 64 || !extra.is_empty() ||
        instance.args.has_non_region_param() || instance.args.has_escaping_bound_vars() ||
        instance.args.has_infer() || instance.args.has_placeholders() || instance.args.references_error() ||
        !super::generic_mir::supported_arguments(instance.args) ||
        !matches!(tcx.def_kind(definition), D::Fn | D::AssocFn) ||
        tcx.is_foreign_item(definition) ||
        tcx.body_codegen_attrs(definition).flags.contains(F::TRACK_CALLER) {
        return None;
    }
    let signature = tcx.fn_sig(definition).instantiate(tcx, instance.args).skip_norm_wip();
    if !signature.bound_vars().is_empty() { return None; }
    let signature = signature.skip_binder();
    if signature.c_variadic() || !matches!(signature.abi(),
        A::Rust | A::RustCold | A::RustPreserveNone | A::RustTail) {
        return None;
    }
    let simple = |ty: ty::Ty<'tcx>| matches!(ty.kind(),
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never)
        || matches!(ty.kind(), ty::Tuple(fields) if fields.is_empty());
    signature.inputs_and_output.iter().all(simple).then_some(signature)
}

pub(super) fn trace(route: &str, queried: bool, instance: ty::Instance<'_>) {
    if std::env::var_os("LEAN_MIRI_TRACE_ABI_CALLS").is_some() {
        eprintln!("lean_miri_instance_abi_call route={route} queried={queried} instance={instance:?}");
    }
}
