//! Syntactic admission for the raw Lean Item FnAbi provider. This reads the
//! declaration signature and raw codegen flags, never layout_of or FnAbi.
use rustc_middle::ty::{self, TyCtxt, TypeVisitableExt};
use rustc_middle::ty::inherent::IntoKind;

// Source grammar proof of a thin pointee. This never asks Sized/layout/traits;
// aliases and unsized tails stay residual. Field recursion is bounded even for
// malformed recursive declarations; pointers stop the traversal.
pub(super) fn sized_pointee<'tcx>(tcx: TyCtxt<'tcx>, input: ty::Ty<'tcx>, fuel: usize) -> bool {
    if fuel == 0 { return false; }
    match input.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never |
        ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..) => true,
        // Pattern refinements preserve their base type sizedness. This proves
        // only pointee thinness; the runtime still computes its exact layout.
        ty::Pat(base, _) => sized_pointee(tcx, *base, fuel - 1),
        ty::Array(element, _) => sized_pointee(tcx, *element, fuel - 1),
        ty::Tuple(fields) => fields.iter().all(|field| sized_pointee(tcx, field, fuel - 1)),
        ty::Adt(definition, arguments) if definition.is_struct() &&
            !definition.repr().simd() && !definition.repr().scalable() =>
            definition.non_enum_variant().fields.iter().all(|field|
                sized_pointee(tcx, field.ty(tcx, arguments).skip_norm_wip(), fuel - 1)),
        _ => false,
    }
}

// Empty source structs have no payload and ABI alignment one unless a raw
// representation attribute raises it. No layout/trait/ABI query is used.
fn empty_allocator(input:ty::Ty<'_>)->bool {
    let ty::Adt(definition,_) = input.kind() else {return false;};
    let repr=definition.repr();
    definition.is_struct() && definition.non_enum_variant().fields.is_empty() &&
        !repr.simd() && !repr.scalable() && repr.align.is_none_or(|align|align.bytes()==1)
}
// Follow the canonical pointer wrappers in the owned-box declaration. This
// also rejects an unrelated or noncanonical lang-item struct with extra data.
fn pointer_storage<'tcx>(tcx:TyCtxt<'tcx>,input:ty::Ty<'tcx>,pointee:ty::Ty<'tcx>,fuel:usize)->bool {
    if fuel==0 {return false;}
    match *input.kind() {
        ty::RawPtr(child,_)|ty::Ref(_,child,_)=>child==pointee,
        ty::Pat(base,pattern) if matches!(pattern.kind(),ty::PatternKind::NotNull)=>
            pointer_storage(tcx,base,pointee,fuel-1),
        ty::Adt(definition,arguments) if definition.is_struct()=>{
            let repr=definition.repr();
            if repr.c()||repr.simd()||repr.scalable()||repr.pack.is_some()||
                !repr.align.is_none_or(|align|align.bytes()==1) {return false;}
            let mut pointers=0;
            for field in &definition.non_enum_variant().fields {
                let field=field.ty(tcx,arguments).skip_norm_wip();
                if empty_allocator(field) {continue;}
                if !pointer_storage(tcx,field,pointee,fuel-1) {return false;}
                pointers+=1;
            }
            pointers==1
        },
        _=>false,
    }
}
pub(super) fn thin_box<'tcx>(tcx:TyCtxt<'tcx>,input:ty::Ty<'tcx>)->bool {
    let ty::Adt(definition,arguments)=*input.kind() else {return false;};
    if !definition.is_box()||!definition.is_struct() {return false;}
    let Some(pointee)=arguments.get(0).and_then(|argument|argument.as_type()) else {return false;};
    let Some(allocator)=arguments.get(1).and_then(|argument|argument.as_type()) else {return false;};
    // The source proof targets a single pointer scalar, not aggregate storage.
    let dl=&tcx.data_layout;
    dl.aggregate_align.bytes()==1 && dl.pointer_align_in(dl.default_address_space).bytes()<=8 &&
        dl.pointer_size_in(dl.default_address_space).bytes()==8 &&
        sized_pointee(tcx,pointee,256)&&empty_allocator(allocator)&&pointer_storage(tcx,input,pointee,256)
}

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
    // Only a syntactically sized pointee is admitted here. This is source
    // grammar classification, not a layout/Sized query. Fat raw pointers and
    // references retain an explicit residual until their full ABI rules exist.
    let simple = |ty: ty::Ty<'tcx>| {
        if !super::generic_mir::supported_arguments(tcx.mk_args(&[ty.into()])) { return false; }
        match ty.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => true,
            ty::Tuple(fields) => fields.is_empty(),
            ty::RawPtr(pointee,_) => sized_pointee(tcx, *pointee, 256),
            ty::Ref(_,pointee,_) => sized_pointee(tcx, *pointee, 256),
            ty::FnPtr(types,header) => types.with(*header).bound_vars().is_empty(),
            ty::Adt(..) => thin_box(tcx,ty),
            _ => false,
        }
    };
    signature.inputs_and_output.iter().all(simple).then_some(signature)
}

pub(super) fn trace(route: &str, queried: bool, instance: ty::Instance<'_>) {
    if std::env::var_os("LEAN_MIRI_TRACE_ABI_CALLS").is_some() {
        eprintln!("lean_miri_instance_abi_call route={route} queried={queried} instance={instance:?}");
    }
}
