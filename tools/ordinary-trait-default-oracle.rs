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
   if tcx.def_kind(local)==DefKind::Struct && tcx.item_name(local.to_def_id()).as_str()=="Wrap" {
    self_ty=Some(tcx.type_of(local).instantiate(tcx,tcx.mk_args(&[tcx.types.u8.into()])).skip_norm_wip());
   }
  }
  let args=tcx.mk_args(&[self_ty.expect("self").into(),tcx.types.u8.into(),tcx.types.u16.into()]);
  let mut rows=Vec::new();
  for method in tcx.associated_items(trait_id.expect("trait")).in_definition_order() {
   if tcx.def_kind(method.def_id)!=DefKind::AssocFn {continue;}
   let value=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),method.def_id,args).expect("selection error").expect("missing concrete instance");
   assert!(matches!(value.def,ty::InstanceKind::Item(_)));
   assert_eq!(value.def_id(),method.def_id,"unoverridden default must retain trait Item");
   assert_eq!(value.args,args,"default leaf must retain original trait3 scope");
   let body=tcx.instance_mir(value.def); assert!(!body.basic_blocks.is_empty());
   assert_eq!(tcx.fn_sig(method.def_id).instantiate(tcx,args).skip_norm_wip().bound_vars().len(),0);
   rows.push(format!("{{\"method\":{},\"arguments\":[{}],\"selected\":{},\"selected_arguments\":[{}]}}",identity(method.def_id),arguments(tcx,args),identity(value.def_id()),arguments(tcx,value.args)));
  }
  println!("{{\"queries\":[{}]}}",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
