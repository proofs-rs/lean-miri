#![feature(rustc_private)]
extern crate rustc_driver; extern crate rustc_hir; extern crate rustc_interface;
extern crate rustc_middle; extern crate rustc_abi;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::def::DefKind;
use rustc_middle::ty::{self,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let root=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_kind(*id)==DefKind::Fn && tcx.item_name(id.to_def_id()).as_str()=="boundary").expect("boundary root");
  let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(root).instantiate_identity().skip_norm_wip());
  assert_eq!(sig.inputs().len(),5);
  let mut rows=Vec::new();
  for (index,input) in sig.inputs().iter().copied().enumerate() {
   let ty::Adt(def,args)=input.kind() else {panic!("not source ADT")};
   let first=def.non_enum_variant().fields.iter().next().expect("field").ty(tcx,args).skip_norm_wip();
   let field_layout=tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(first)).expect("actual field layout");
   assert_eq!(field_layout.is_1zst(),index==0,"field non1ZST distinction case{index}");
   rows.push(format!("{{\"index\":{index},\"one_zst\":{},\"size_bytes\":{},\"align_bytes\":{}}}",field_layout.is_1zst(),field_layout.size.bytes(),field_layout.align.abi.bytes()));
  }
  println!("{{\"fields\":[{}]}}",rows.join(","));
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
