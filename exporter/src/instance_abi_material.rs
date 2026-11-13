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

// Two primitive nonpointer fields. Position-dependent return indirection is
// reconstructed in Lean; no layout/FnAbi query selects this source domain.
pub(super) fn small_nonpointer_pair(input: ty::Ty<'_>) -> bool {
    let ty::Tuple(fields) = input.kind() else { return false; };
    fields.len() == 2 && fields.iter().all(|field| match field.kind() {
        ty::Bool | ty::Char => true,
        ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
        _ => false,
    })
}

// Source-only wide raw pointers with canonical usize metadata. Dynamic,
// borrowed and unsized-struct tails remain exact material residuals.
pub(super) fn raw_slice_pointer<'tcx>(tcx: TyCtxt<'tcx>, input: ty::Ty<'tcx>) -> bool {
    let ty::RawPtr(pointee,_) = input.kind() else { return false; };
    let dl = &tcx.data_layout;
    if dl.default_address_space != rustc_abi::AddressSpace::ZERO ||
        dl.pointer_size_in(rustc_abi::AddressSpace::ZERO).bytes() != 8 ||
        dl.pointer_align_in(rustc_abi::AddressSpace::ZERO).bytes() > 8 ||
        dl.i64_align.bytes() > 8 || dl.aggregate_align.bytes() > 8 { return false; }
    match pointee.kind() {
        ty::Str => true,
        ty::Slice(element) => sized_pointee(tcx,*element,256),
        _ => false,
    }
}

// Direct tuple ScalarPairs with raw data pointers. These target alignment
// bounds ensure two register-sized fields occupy at most sixteen bytes, so
// neither Item return deduction nor the external indirect policy is needed.
pub(super) fn small_raw_pointer_pair<'tcx>(tcx: TyCtxt<'tcx>, input: ty::Ty<'tcx>) -> bool {
    let ty::Tuple(fields) = input.kind() else { return false; };
    if fields.len() != 2 { return false; }
    let dl = &tcx.data_layout;
    if dl.default_address_space != rustc_abi::AddressSpace::ZERO ||
        dl.pointer_size_in(rustc_abi::AddressSpace::ZERO).bytes() != 8 ||
        dl.pointer_align_in(rustc_abi::AddressSpace::ZERO).bytes() > 8 ||
        [dl.aggregate_align,dl.i8_align,dl.i16_align,dl.i32_align,dl.i64_align,
            dl.f16_align,dl.f32_align,dl.f64_align].iter().any(|align|align.bytes()>8) {
        return false;
    }
    let mut raw = false;
    fields.iter().all(|field|match field.kind() {
        ty::RawPtr(pointee,_) => {raw=true;sized_pointee(tcx,*pointee,256)},
        ty::Bool | ty::Char => true,
        ty::Int(kind) => !matches!(kind,ty::IntTy::I128),
        ty::Uint(kind) => !matches!(kind,ty::UintTy::U128),
        ty::Float(kind) => !matches!(kind,ty::FloatTy::F128),
        _ => false,
    }) && raw
}

// Bounded byte-array/tuple source grammar for direct and indirect Memory.
// Raw value-tree bits establish the count, never layout_of or ABI results.
pub(super) fn small_memory(input: ty::Ty<'_>) -> bool {
    let byte = |field: ty::Ty<'_>| matches!(field.kind(),
        ty::Bool | ty::Uint(ty::UintTy::U8) | ty::Int(ty::IntTy::I8));
    match input.kind() {
        ty::Tuple(fields) => (3..=32).contains(&fields.len()) && fields.iter().all(byte),
        ty::Array(element, count) if byte(*element) => {
            let ty::ConstKind::Value(value) = count.kind() else { return false; };
            let ty::ValTreeKind::Leaf(scalar) = **value.valtree else { return false; };
            scalar.to_bits_unchecked() <= 32
        },
        _ => false,
    }
}

// RustTail indirect arguments require stack-offset lowering, still residual.
// Reject only its aggregate inputs conservatively from raw source grammar.
pub(super) fn tail_direct(input: ty::Ty<'_>) -> bool {
    match input.kind() {
        // Admitted primitive ScalarPair arguments stay direct at every size.
        ty::Tuple(fields) if fields.len() == 2 => true,
        ty::Tuple(fields) => fields.len() <= 8,
        ty::Array(_, count) => {
            let ty::ConstKind::Value(value) = count.kind() else { return false; };
            let ty::ValTreeKind::Leaf(scalar) = **value.valtree else { return false; };
            scalar.to_bits_unchecked() <= 8
        },
        _ => true,
    }
}

// Only the newly admitted indirect domains need MIR-deduced attributes.
// Dependency metadata was produced using that crate's original options, not
// this session's optimization/incremental flags. Keep its exact FnAbi query.
fn newly_indirect(input: ty::Ty<'_>, is_return: bool) -> bool {
    match input.kind() {
        ty::Array(_, count) if small_memory(input) => {
            let ty::ConstKind::Value(value) = count.kind() else { return false; };
            let ty::ValTreeKind::Leaf(scalar) = **value.valtree else { return false; };
            scalar.to_bits_unchecked() > 8
        },
        ty::Tuple(fields) if small_memory(input) => fields.len() > 8,
        ty::Tuple(fields) if is_return && small_nonpointer_pair(input) =>
            fields.iter().any(|field| matches!(field.kind(),
                ty::Int(ty::IntTy::I128) | ty::Uint(ty::UintTy::U128) |
                ty::Float(ty::FloatTy::F128))),
        _ => false,
    }
}

pub(super) fn signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>,
    extra: &'tcx ty::List<ty::Ty<'tcx>>) -> Option<ty::FnSig<'tcx>> {
    use rustc_abi::ExternAbi as A;
    use rustc_hir::def::DefKind as D;
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
    if matches!(instance.def, ty::InstanceKind::Virtual(..)) {
        return virtual_signature(tcx,instance,extra);
    }
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
    if signature.abi() == A::RustTail && !signature.inputs().iter().all(|input| tail_direct(*input)) {
        return None;
    }
    if !definition.is_local() && (newly_indirect(signature.output(), true) ||
        signature.inputs().iter().any(|input| newly_indirect(*input, false))) {
        return None;
    }
    // Source pointee syntax selects thin pointers and slice/str raw pointers.
    // Borrowed wide pointers and other unsized tails remain material residuals;
    // no layout/Sized query answer selects this domain.
    let simple = |ty: ty::Ty<'tcx>| {
        if !super::generic_mir::supported_arguments(tcx.mk_args(&[ty.into()])) { return false; }
        match ty.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => true,
            ty::Tuple(fields) => fields.is_empty() || small_nonpointer_pair(ty) ||
                small_raw_pointer_pair(tcx,ty) || small_memory(ty),
            ty::Array(..) => small_memory(ty),
            ty::RawPtr(pointee,_) => sized_pointee(tcx, *pointee, 256) || raw_slice_pointer(tcx,ty),
            ty::Ref(_,pointee,_) => sized_pointee(tcx, *pointee, 256),
            ty::FnPtr(types,header) => types.with(*header).bound_vars().is_empty(),
            ty::Adt(..) => thin_box(tcx,ty),
            _ => false,
        }
    };
    signature.inputs_and_output.iter().all(simple).then_some(signature)
}

// Ordinary Virtual ABI, not a VTable shim: the first argument retains its
// source type while abi.rs::make_thin_self_ptr replaces its layout with *mut().
fn virtual_signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>,
    extra: &'tcx ty::List<ty::Ty<'tcx>>) -> Option<ty::FnSig<'tcx>> {
    use rustc_abi::ExternAbi as A;
    use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags as F;
    let ty::InstanceKind::Virtual(definition,_) = instance.def else {return None;};
    if tcx.sess.target.arch != rustc_target::spec::Arch::X86_64 ||
        tcx.sess.target.pointer_width != 64 || !extra.is_empty() ||
        instance.args.has_non_region_param() || instance.args.has_escaping_bound_vars() ||
        instance.args.has_infer() || instance.args.has_placeholders() || instance.args.references_error() ||
        tcx.body_codegen_attrs(definition).flags.contains(F::TRACK_CALLER) ||
        tcx.data_layout.default_address_space != rustc_abi::AddressSpace::ZERO {
        return None;
    }
    let bound = tcx.fn_sig(definition).instantiate(tcx,instance.args).skip_norm_wip();
    if !bound.bound_vars().iter().all(|v|matches!(v,ty::BoundVariableKind::Region(_))) {return None;}
    let sig = tcx.instantiate_bound_regions_with_erased(bound);
    if sig.c_variadic() || !matches!(sig.abi(),A::Rust|A::RustCold|A::RustPreserveNone|A::RustTail) {return None;}
    let first = *sig.inputs().first()?;
    let child = match first.kind() {
        ty::Ref(_,child,_)|ty::RawPtr(child,_) => *child,
        _=>return None,
    };
    if !matches!(child.kind(),ty::Dynamic(..)) {return None;}
    let simple = |input:ty::Ty<'tcx>| {
        if !super::generic_mir::supported_arguments(tcx.mk_args(&[input.into()])) {return false;}
        match input.kind() {
            ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Float(_)|ty::Never=>true,
            ty::Tuple(fields)=>fields.is_empty()||small_nonpointer_pair(input)||small_raw_pointer_pair(tcx,input)||
                (fields.len()<=8 && small_memory(input)),
            ty::Array(..)=>small_memory(input)&&tail_direct(input),
            ty::RawPtr(child,_)=>sized_pointee(tcx,*child,256)||raw_slice_pointer(tcx,input),
            ty::Ref(_,child,_)=>sized_pointee(tcx,*child,256),
            ty::FnPtr(signature,header)=>signature.with(*header).bound_vars().is_empty(),
            _=>false,
        }
    };
    (sig.inputs()[1..].iter().all(|&input|simple(input)) && simple(sig.output()) &&
        !newly_indirect(sig.output(),true)).then_some(sig)
}

pub(super) fn trace(route: &str, queried: bool, instance: ty::Instance<'_>) {
    if std::env::var_os("LEAN_MIRI_TRACE_ABI_CALLS").is_some() {
        eprintln!("lean_miri_instance_abi_call route={route} queried={queried} instance={instance:?}");
    }
}
