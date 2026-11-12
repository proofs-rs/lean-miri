#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_const_eval;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,Ty,TyCtxt};
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let find=|name:&str|tcx.hir_crate_items(()).definitions().find(|&d|tcx.def_kind(d)==DefKind::Struct&&tcx.item_name(d.to_def_id()).as_str()==name).unwrap().to_def_id();
  let specifications=[("U8",tcx.types.u8,0),("U8",tcx.types.u8,2),("U8",tcx.types.u8,255),
   ("I8",tcx.types.i8,128),("I8",tcx.types.i8,127),("I8",tcx.types.i8,255),
   ("Wide",tcx.types.u128,u128::MAX),("Pointer",tcx.types.usize,tcx.data_layout.pointer_size().unsigned_int_max()),
   ("Boolean",tcx.types.bool,1)];
  let rows=specifications.into_iter().map(|(name,kind,bits)|{
   let value=ty::Const::from_bits(tcx,bits,ty::TypingEnv::fully_monomorphized(),kind);
   let ty=Ty::new_adt(tcx,tcx.adt_def(find(name)),tcx.mk_args(&[value.into()]));
   format!("{{\"type\":{},\"display\":{:?},\"intrinsic\":{:?}}}",generic_material::type_tree(tcx,ty).unwrap(),ty.to_string(),rustc_const_eval::util::type_name(tcx,ty))
  }).collect::<Vec<_>>();
  println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args:Vec<_>=std::env::args().collect();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
