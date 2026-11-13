// Independent pinned-rustc raw MIR oracle. Compile with rustc_private and run
// with the recorded std source-trait-call rustc arguments. Physical IDs are
// guarded by exact paths; this is a finite fixture oracle, not a general selector.
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
  let id=DefId{krate:CrateNum::from_u32(2),index:DefIndex::from_u32(69102)};
  assert_eq!(tcx.def_path_str(id),"core::num::niche_types::NonZeroU64Inner::{constant#0}");
  let mut frame=ty::Instance::mono(tcx,id);
  for depth in 0..5 {
   assert!(tcx.trivial_const(frame.def_id()).is_none(), "required raw root unexpectedly trivial");
   println!("has_mir_available={}",tcx.is_mir_available(frame.def_id()));
   let body=tcx.mir_for_ctfe(frame.def_id());
   println!("frame{depth}={frame:?} return={:?} phase={:?} args={} required={:?}",body.local_decls[rustc_middle::mir::RETURN_PLACE].ty,body.phase,body.arg_count,body.required_consts);
   for (n,block) in body.basic_blocks.iter().enumerate(){println!("bb{n} statements={:#?} terminator={:#?}",block.statements,block.terminator());}
   let required=body.required_consts.as_ref().unwrap();
   let Some(c)=required.first() else {break};
   let rustc_middle::mir::Const::Unevaluated(source,declared)=c.const_ else{panic!("nonUnevaluated dependency {:?}",c.const_)};
   println!("dependency_type={declared:?} source={source:?}");
   frame=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),source.def,source.args).expect("oracle select error").expect("oracle no selected const");
  }
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
