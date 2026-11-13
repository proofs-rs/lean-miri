#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::ty::{self,TyCtxt};
fn identity(d:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",d.krate.as_u32(),d.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,a:ty::GenericArgsRef<'tcx>)->String {
 a.iter().map(|v|generic_material::argument(tcx,v).expect("raw argument")).collect::<Vec<_>>().join(",")
}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let mut trait_id=None;let mut self_ty=None;
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)==DefKind::Trait && tcx.item_name(local.to_def_id()).as_str()=="Compute" {trait_id=Some(local.to_def_id());}
   if tcx.def_kind(local)==DefKind::Fn && tcx.item_name(local.to_def_id()).as_str()=="query_method" {
    let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(local).instantiate_identity().skip_norm_wip());
    let ty::Ref(_,ty,_) = *sig.inputs()[0].kind() else {panic!("query receiver")};self_ty=Some(ty);
   }
  }
  let args=tcx.mk_args(&[self_ty.expect("self").into(),tcx.types.u8.into(),tcx.types.u16.into()]);
  let mut rows=Vec::new();
  for method in tcx.associated_items(trait_id.expect("trait")).in_definition_order() {
   if tcx.def_kind(method.def_id)!=DefKind::AssocFn {continue;}
   let value=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),method.def_id,args).expect("selection error").expect("missing concrete instance");
   assert!(matches!(value.def,ty::InstanceKind::Item(_)));
   rows.push(format!("{{\"method\":{},\"arguments\":[{}],\"selected\":{},\"selected_arguments\":[{}]}}",identity(method.def_id),arguments(tcx,args),identity(value.def_id()),arguments(tcx,value.args)));
  }
  println!("{{\"queries\":[{}]}}",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
