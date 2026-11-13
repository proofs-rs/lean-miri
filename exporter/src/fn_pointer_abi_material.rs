//! Source grammar admission for independent function-pointer ABIs.
//! No normalization, trait, layout or ABI query answers select this domain.
use rustc_middle::ty::{self,TyCtxt,TypeVisitableExt};
// WorldFunctionPointerAbi reifies the COMPLETE signature before erasure and
// normalization. A nested pointer's children are therefore syntax dependencies
// even though its eventual physical argument is just a scalar pointer. Keep
// unsupported constructors as exact material residuals; physical size alone
// cannot establish that the source query can reconstruct its complete key.
fn reifiable_type(input:ty::Ty<'_>,fuel:usize)->bool {
    if fuel==0 {return false;}
    match *input.kind() {
        ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Float(_)|ty::Never|ty::Str=>true,
        ty::RawPtr(child,_)|ty::Ref(_,child,_)|ty::Slice(child)=>reifiable_type(child,fuel-1),
        ty::Array(child,length)=>reifiable_type(child,fuel-1)&&reifiable_constant(length,fuel-1),
        ty::Tuple(children)=>children.iter().all(|child|reifiable_type(child,fuel-1)),
        ty::Adt(_,arguments)=>reifiable_arguments(arguments,fuel-1),
        ty::FnDef(_,arguments)=>arguments.bound_vars().is_empty()&&
            reifiable_arguments(arguments.skip_binder(),fuel-1),
        ty::FnPtr(signature,header)=>{
            let signature=signature.with(header);
            signature.bound_vars().iter().all(|value|matches!(value,ty::BoundVariableKind::Region(_)))&&
                signature.skip_binder().inputs_and_output.iter().all(|child|reifiable_type(child,fuel-1))
        },
        // Aliases require a separately admitted normalization/obligation domain.
        // Dyn, pattern/unsafe-binder and opaque foreign keys are not admitted.
        _=>false,
    }
}
fn reifiable_arguments(arguments:ty::GenericArgsRef<'_>,fuel:usize)->bool {
    if fuel==0 {return false;}
    arguments.iter().all(|argument|match argument.kind(){
        ty::GenericArgKind::Type(child)=>reifiable_type(child,fuel-1),
        ty::GenericArgKind::Const(value)=>reifiable_constant(value,fuel-1),
        ty::GenericArgKind::Lifetime(_)=>true,
    })
}
fn reifiable_constant(value:ty::Const<'_>,fuel:usize)->bool {
    if fuel==0 {return false;}
    let ty::ConstKind::Value(value)=value.kind() else {return false;};
    reifiable_type(value.ty,fuel-1)&&match **value.valtree {
        ty::ValTreeKind::Leaf(_)=>true,
        ty::ValTreeKind::Branch(children)=>children.iter().all(|child|reifiable_constant(child,fuel-1)),
    }
}
pub(super) fn signature<'tcx>(tcx:TyCtxt<'tcx>, signature:ty::PolyFnSig<'tcx>,
    extra:&'tcx ty::List<ty::Ty<'tcx>>) -> Option<ty::FnSig<'tcx>> {
    use rustc_abi::ExternAbi as A;
    if tcx.sess.target.arch != rustc_target::spec::Arch::X86_64 ||
        tcx.sess.target.pointer_width != 64 || !extra.is_empty() ||
        signature.has_non_region_param() || signature.has_escaping_bound_vars() ||
        signature.has_infer() || signature.has_placeholders() || signature.references_error() ||
        !signature.bound_vars().iter().all(|value|matches!(value,ty::BoundVariableKind::Region(_))) {
        return None;
    }
    let signature=signature.skip_binder();
    if !signature.inputs_and_output.iter().all(|input|reifiable_type(input,256)) {return None;}
    if signature.c_variadic() || !matches!(signature.abi(),
        A::Rust|A::RustCold|A::RustPreserveNone|A::RustTail) {return None;}
    if signature.abi()==A::RustTail && !signature.inputs().iter().all(|input|
        super::instance_abi_material::tail_direct(*input)) {return None;}
    signature.inputs_and_output.iter().all(|input| match input.kind() {
        ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Float(_)|ty::Never => true,
        ty::Tuple(fields)=>fields.is_empty()||super::instance_abi_material::small_nonpointer_pair(input)||
            super::instance_abi_material::small_memory(input),
        ty::Array(..)=>super::instance_abi_material::small_memory(input),
        ty::RawPtr(child,_)|ty::Ref(_,child,_)=>super::instance_abi_material::sized_pointee(tcx,*child,256),
        ty::FnPtr(..)=>true,
        ty::Adt(..)=>super::instance_abi_material::thin_box(tcx,input),
        _=>false,
    }).then_some(signature)
}
pub(super) fn trace(route:&str,queried:bool,signature:ty::PolyFnSig<'_>,extra:&ty::List<ty::Ty<'_>>) {
    if std::env::var_os("LEAN_MIRI_TRACE_ABI_CALLS").is_some() {
        eprintln!("lean_miri_fn_pointer_abi_call route={route} queried={queried} signature={signature:?} extra={extra:?}");
    }
}
