#![feature(rustc_private)]
extern crate rustc_driver; extern crate rustc_hir; extern crate rustc_interface; extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};use rustc_hir::def::DefKind;use rustc_middle::ty::{self,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let env=ty::TypingEnv::fully_monomorphized();let mut rows=Vec::new();
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)!=DefKind::Fn {continue;}
   let symbol=tcx.item_name(local.to_def_id());let name=symbol.as_str();if !name.starts_with("query_"){continue;}
   let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(local).instantiate_identity().skip_norm_wip());
   let ty::Ref(_,object,_) = *sig.inputs()[0].kind() else {panic!("query reference")};
   rows.push(format!("{{\"name\":\"{}\",\"dynamic\":{},\"freeze\":{},\"unpin\":{},\"unsafe_unpin\":{}}}",name,generic_material::type_tree(tcx,object).expect("rawdyn"),object.is_freeze(tcx,env),object.is_unpin(tcx,env),object.is_unsafe_unpin(tcx,env)));
  }
  println!("{{\"queries\":[{}]}}",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
