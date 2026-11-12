//! Raw method-signature/definition source for FnPtr pointer conversion shims.
//! Eligibility and interface extraction never request instance_mir.
use rustc_middle::{mir,ty::{self,TyCtxt}};
use rustc_middle::ty::TypeVisitableExt;

pub fn self_type<'tcx>(instance:ty::Instance<'tcx>)->Option<ty::Ty<'tcx>> {
    match instance.def {
        ty::InstanceKind::Shim(ty::ShimKind::FnPtrAsPtr(_,ty)|ty::ShimKind::FnPtrFromPtr(_,ty))=>Some(ty),
        _=>None,
    }
}

pub fn eligible<'tcx>(tcx:TyCtxt<'tcx>,instance:ty::Instance<'tcx>)->bool {
    let Some(self_ty)=self_type(instance) else {return false};
    if instance.args.len()!=1 || instance.args.type_at(0)!=self_ty {return false}
    if self_ty.has_non_region_param() || self_ty.has_escaping_bound_vars() || self_ty.has_infer()
        || self_ty.has_placeholders() || self_ty.references_error() {return false}
    let ty::FnPtr(signature,header)=self_ty.kind() else {return false};
    let signature=signature.with(*header);
    if !signature.bound_vars().is_empty() {return false}
    let signature=signature.skip_binder();
    if !signature.inputs_and_output.iter().all(|ty|
        super::generic_mir::supported_arguments(tcx.mk_args(&[ty.into()]))) {return false}
    let method=tcx.fn_sig(instance.def.def_id()).instantiate_identity().skip_norm_wip();
    method.bound_vars().is_empty() && method.skip_binder().inputs().len()==1
}

pub fn interface<'tcx>(tcx:TyCtxt<'tcx>,instance:ty::Instance<'tcx>)
    ->Result<super::generic_mir::Interface<'tcx>,String> {
    if !eligible(tcx,instance) {return Err("FnPtr conversion shim is outside raw signature domain".into())}
    let self_ty=self_type(instance).unwrap();
    let signature=tcx.fn_sig(instance.def.def_id()).instantiate(tcx,&[self_ty.into()]).skip_norm_wip();
    let signature=signature.no_bound_vars().ok_or("FnPtr conversion method has bound variables")?;
    Ok(super::generic_mir::Interface {argument_count:1,spread_argument:None,
        arguments:vec![(mir::Local::from_u32(1),signature.inputs()[0])],return_type:signature.output()})
}
