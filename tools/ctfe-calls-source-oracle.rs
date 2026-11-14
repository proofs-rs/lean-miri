//! Real scalar-frame stepping only. The public inspection-context factory uses
//! CheckAlignment::No; this pointer-free corpus never dereferences memory.
//! The private zero-argument query-root setup, validation and interning are not
//! being replicated or established by this probe.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_abi;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_const_eval;
extern crate rustc_hir;
extern crate rustc_span;
extern crate serde_json;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{ty,mir};
use rustc_const_eval::interpret::{ReturnContinuation,MemoryKind};

#[path="../exporter/src/ctfe_calls_source.rs"] mod call_source;
#[path="../exporter/src/ctfe_scalar_source.rs"] mod scalar_source;
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let local=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="root_call").unwrap();
  let id=local.to_def_id();let instance=ty::Instance::mono(tcx,id);let env=ty::TypingEnv::fully_monomorphized();let body=tcx.mir_for_ctfe(id);
  for (index,constant) in body.required_consts().iter().enumerate() {println!("required\t{index}\t{:?}",constant.const_);}
  let mut encoded=Vec::new();let mut spans=Vec::new();let mut definitions=Vec::new();
  for name in ["INPUT","arithmetic","root_call","ROOT"] {
   let definition=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())==name).unwrap().to_def_id();
   definitions.push(serde_json::json!({"definition":{"crate":0,"index":definition.index.as_u32()},"name":name}));
   let mut span=|span|{if let Some(index)=spans.iter().position(|value|*value==span){index as u64}else{let index=spans.len();spans.push(span);index as u64}};
   encoded.push(scalar_source::capture(tcx,definition,None,tcx.mir_for_ctfe(definition),&mut span).or_else(|_|call_source::capture(tcx,definition,None,tcx.mir_for_ctfe(definition),&mut span)).unwrap());
  }
  let output=std::env::var("CTFE_CALLS_SOURCE").expect("CTFE_CALLS_SOURCE output path");
  std::fs::write(output,serde_json::to_vec_pretty(&serde_json::json!({"sources":encoded,"definitions":definitions,"span_count":spans.len()})).unwrap()).unwrap();
  let input=std::env::var("LEAN_MIRI_CTFE_SCALAR_INPUT").unwrap_or("9".into()).parse::<u32>().unwrap();
  let value=mir::ConstValue::Scalar(mir::interpret::Scalar::from_u32(input));
  let (mut ecx,argument)=rustc_const_eval::const_eval::mk_eval_cx_for_const_val(tcx.at(tcx.def_span(id)),env,value,tcx.types.u32).unwrap();
  let ret=ecx.allocate(argument.layout,MemoryKind::Stack).report_err().unwrap();
  let abi=tcx.fn_abi_of_instance(env.as_query_input((instance,ty::List::empty()))).unwrap();
  ecx.init_stack_frame(instance,body,abi,&[],false,&ret.clone().into(),ReturnContinuation::Stop {cleanup:false}).report_err().unwrap();
  let mut steps=0;let mut counters=0;
  loop {
   let loc=ecx.frame().current_loc().left().unwrap();
   let block=&ecx.body().basic_blocks[loc.block];
   let counter=block.statements.get(loc.statement_index).is_some_and(|s|matches!(s.kind,mir::StatementKind::ConstEvalCounter));
   let returning=ecx.frame_idx()==0 && loc.statement_index==block.statements.len() && matches!(block.terminator().kind,mir::TerminatorKind::Return);
   println!("step\t{steps}\t{}\t{}\t{}\t{counter}",tcx.def_path_str(ecx.frame().instance().def_id()),loc.block.as_u32(),loc.statement_index);
   if counter {counters+=1;}
   match ecx.step().report_err() {
    Ok(true)=>{steps+=1;},
    Ok(false)=>panic!("unexpected empty stack before root return"),
    Err(error)=>{println!("error\t{steps}\t{counters}\t{error:?}");return Compilation::Stop;}
   }
   if returning {break;}
  }
  let result=ecx.read_scalar(&ret).report_err().unwrap();
  println!("result\t{steps}\t{counters}\t{result:?}");
  Compilation::Stop
 }
}
fn main(){rustc_driver::compiler_entrypoint(&std::env::args().collect::<Vec<_>>(),&mut Oracle)}
