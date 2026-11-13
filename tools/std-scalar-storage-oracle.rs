#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::def_id::{CrateNum,DefId,DefIndex};
use rustc_middle::ty::{self,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  // Physical identity from the exact source document; path check guards a
  // different crate load/order/sysroot. No imported layout sizes are read.
  let id=DefId{krate:CrateNum::from_u32(2),index:DefIndex::from_u32(36728)};
  assert_eq!(tcx.def_path_str(id),"core::num::niche_types::UsizeNoHighBit");
  let adt=tcx.adt_def(id); assert!(adt.repr().transparent());
  let args=tcx.mk_args(&[]);let parent=ty::Ty::new_adt(tcx,adt,args);
  assert_eq!(adt.non_enum_variant().fields.len(),1);
  let field=adt.non_enum_variant().fields.iter().next().unwrap().ty(tcx,args).skip_norm_wip();
  let ty::Pat(base,_)=*field.kind() else{panic!("raw single field must be Pattern")};
  assert!(base.is_usize());let env=ty::TypingEnv::fully_monomorphized();
  let sizes=[parent,field,base].map(|ty|tcx.layout_of(env.as_query_input(ty)).expect("actual layout oracle").size.bytes());
  assert_eq!(sizes[0],sizes[1]);assert_eq!(sizes[1],sizes[2]);
  println!("{{\"definition\":{{\"crate\":2,\"index\":36728}},\"parent_bytes\":{},\"field_bytes\":{},\"base_bytes\":{}}}",sizes[0],sizes[1],sizes[2]);Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
