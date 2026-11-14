#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty};
struct Probe;
impl Callbacks for Probe {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let before=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert_eq!(before,tcx.lean_miri_complete_allocation_identity_snapshot());
  let def=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_kind(id.to_def_id())==rustc_hir::def::DefKind::AssocConst && tcx.item_name(id.to_def_id()).as_str()=="ANCHOR").unwrap().to_def_id();
  let env=ty::TypingEnv::fully_monomorphized();
  let arg=ty::Const::from_bits(tcx,6,env,tcx.types.u32);
  let instance=ty::Instance::new_raw(def,tcx.mk_args(&[arg.into()]));
  let result=tcx.eval_to_allocation_raw(env.as_query_input(mir::interpret::GlobalId {instance,promoted:None})).unwrap();
  assert!(!before.1.iter().any(|(id,_)|*id==result.alloc_id));
  let after=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert_eq!(after,tcx.lean_miri_complete_allocation_identity_snapshot());
  assert!(after.1.iter().any(|(id,_)|*id==result.alloc_id));
  let memory=tcx.global_alloc(result.alloc_id).unwrap_memory();
  assert!(!memory.inner().mutability.is_mut());
  let fresh=tcx.reserve_and_set_memory_alloc(memory);
  let key=tcx.reserve_and_set_memory_dedup(memory,0);
  assert_eq!(key,tcx.reserve_and_set_memory_dedup(memory,0));
  let complete=tcx.lean_miri_complete_allocation_identity_snapshot();
  assert!(complete.1.iter().any(|(id,_)|*id==fresh));
  assert!(!complete.2.iter().any(|(_,_,id)|*id==fresh));
  assert!(complete.2.iter().any(|(_,salt,id)|*salt==0&&*id==key));
  assert_eq!(complete,tcx.lean_miri_complete_allocation_identity_snapshot());
  println!("PASS actual patched snapshot: before={} after={} root={:?} fresh={fresh:?} dedup={key:?}; repeated snapshots do not mutate complete maps/frontier",before.0,after.0,result.alloc_id);
  Compilation::Stop
 }
}
fn main(){rustc_driver::compiler_entrypoint(&std::env::args().collect::<Vec<_>>(),&mut Probe)}
