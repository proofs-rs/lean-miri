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
use rustc_const_eval::interpret::{FnArg,ReturnContinuation,MemoryKind};

#[path="../exporter/src/ctfe_calls_source.rs"] mod call_source;
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let local=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="callee").unwrap();
  let id=local.to_def_id();let name=std::env::var("CTFE_PREAMBLE_TYPE").unwrap_or("Good".into());
  let argument_definition=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())==name).unwrap().to_def_id();
  let arguments=tcx.mk_args(&[tcx.type_of(argument_definition).instantiate_identity().skip_norm_wip().into()]);
  let instance=ty::Instance::new_raw(id,arguments);let env=ty::TypingEnv::fully_monomorphized();let body=tcx.mir_for_ctfe(id);
  for (index,constant) in body.required_consts().iter().enumerate() {println!("required\t{index}\t{:?}",constant.const_);}
  let mut captured=Vec::new();let mut rules=Vec::new();let mut definitions=Vec::new();let mut spans=Vec::new();
  for local in tcx.hir_crate_items(()).definitions() {
   let definition=local.to_def_id();let path=tcx.def_path_str(definition);
   definitions.push(serde_json::json!({"definition":{"crate":0,"index":definition.index.as_u32()},"name":path}));
   let mut capture=false;
   if path=="callee" || path=="divide" {capture=true;}
   if tcx.def_kind(definition)==rustc_hir::def::DefKind::AssocConst {
    let item=tcx.associated_item(definition);
    if let Some(declaration)=item.trait_item_def_id() {
     let self_ty=tcx.type_of(tcx.parent(definition)).instantiate_identity().skip_norm_wip();
     let ty::Adt(adt,args)=self_ty.kind() else {panic!("non-ADT source impl")};assert!(args.is_empty());
     rules.push(serde_json::json!({"declaration":declaration.index.as_u32(),"self_type":adt.did().index.as_u32(),"value_definition":definition.index.as_u32()}));
     capture=true;
    }
   }
   if capture {captured.push(call_source::capture(tcx,definition,None,tcx.mir_for_ctfe(definition),|span|{if let Some(index)=spans.iter().position(|value|*value==span){index as u64}else{let index=spans.len();spans.push(span);index as u64}}).unwrap());}
  }
  let output=std::env::var("CTFE_PREAMBLE_SOURCE").expect("CTFE_PREAMBLE_SOURCE path");
  std::fs::write(output,serde_json::to_vec_pretty(&serde_json::json!({"sources":captured,"rules":rules,"definitions":definitions,"span_count":spans.len()})).unwrap()).unwrap();
  let input=std::env::var("LEAN_MIRI_CTFE_SCALAR_INPUT").unwrap_or("9".into()).parse::<u32>().unwrap();
  let value=mir::ConstValue::Scalar(mir::interpret::Scalar::from_u32(input));
  let (mut ecx,argument)=rustc_const_eval::const_eval::mk_eval_cx_for_const_val(tcx.at(tcx.def_span(id)),env,value,tcx.types.u32).unwrap();
  let ret=ecx.allocate(argument.layout,MemoryKind::Stack).report_err().unwrap();
  let abi=tcx.fn_abi_of_instance(env.as_query_input((instance,ty::List::empty()))).unwrap();
  let initialized=ecx.init_stack_frame(instance,body,abi,&[FnArg::Copy(argument)],false,&ret.clone().into(),ReturnContinuation::Stop {cleanup:false}).report_err();
  match initialized {
   Ok(())=>println!("preamble\tok\t{:?}",ecx.frame().current_loc()),
   Err(error)=>{println!("preamble\terror\t{:?}\t{error:?}",ecx.frame().current_loc());return Compilation::Stop;}
  }
  let mut steps=0;let mut counters=0;
  loop {
   let loc=ecx.frame().current_loc().left().unwrap();
   let block=&ecx.body().basic_blocks[loc.block];
   let counter=block.statements.get(loc.statement_index).is_some_and(|s|matches!(s.kind,mir::StatementKind::ConstEvalCounter));
   let returning=loc.statement_index==block.statements.len() && matches!(block.terminator().kind,mir::TerminatorKind::Return);
   println!("step\t{steps}\t{}\t{}\t{counter}",loc.block.as_u32(),loc.statement_index);
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
