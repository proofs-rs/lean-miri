//! Actual public raw-allocation/value provider references for fresh const-generic
//! globals. These are observations, never producer answers for the source machine.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_const_eval;
extern crate rustc_hir;
extern crate rustc_abi;
extern crate rustc_span;
extern crate serde_json;
#[path="../exporter/src/ctfe_calls_source.rs"] mod call_source;
#[path="../exporter/src/ctfe_scalar_source.rs"] mod scalar_source;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty};
use rustc_abi::Size;
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let value=std::env::var("CTFE_INTERN_INPUT").unwrap_or("9".into()).parse::<u32>().unwrap();
  let env=ty::TypingEnv::fully_monomorphized();
  let argument=ty::Const::from_bits(tcx,u128::from(value),env,tcx.types.u32);
  let arguments=tcx.mk_args(&[argument.into()]);
  let mut spans=Vec::new();let mut sources=Vec::new();let mut definitions=Vec::new();
  for local in tcx.hir_crate_items(()).definitions() {
   let definition=local.to_def_id();
   if !matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Fn|rustc_hir::def::DefKind::AssocConst) {continue}
   let symbol=tcx.item_name(definition);let name=symbol.as_str();
   if !["ROOT","SAME","arithmetic"].contains(&name) {continue}
   let body=tcx.mir_for_ctfe(definition);
   let mut span=|span|{if let Some(index)=spans.iter().position(|old|*old==span){index as u64}else{let index=spans.len();spans.push(span);index as u64}};
   let captured=if name=="arithmetic" {scalar_source::capture(tcx,definition,None,body,&mut span)} else {call_source::capture_const_args(tcx,definition,None,body,&mut span)}.unwrap();
   definitions.push(serde_json::json!({"definition":{"crate":0,"index":definition.index.as_u32()},"name":name}));sources.push(captured);
  }
  std::fs::write(std::env::var("CTFE_CONST_ARGS_SOURCE").expect("source output"),serde_json::to_vec_pretty(&serde_json::json!({"sources":sources,"definitions":definitions,"span_count":spans.len()})).unwrap()).unwrap();
  let mut results=Vec::new();
  for name in ["ROOT","SAME"] {
   let definition=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_kind(id.to_def_id())==rustc_hir::def::DefKind::AssocConst && tcx.item_name(id.to_def_id()).as_str()==name).unwrap().to_def_id();
   let instance=ty::Instance::new_raw(definition,arguments);
   let global=mir::interpret::GlobalId {instance,promoted:None};
   let result=match tcx.eval_to_allocation_raw(env.as_query_input(global)) {
    Ok(result)=>result,
    Err(error)=>{println!("allocation-error\t{name}\tinput={value}\t{error:?}");return Compilation::Stop;}
   };
   assert_eq!(result.ty,tcx.types.u32);
   let payload=tcx.global_alloc(result.alloc_id).unwrap_memory();
   assert!(!payload.inner().mutability.is_mut());
   assert_eq!(payload.inner().size(),Size::from_bytes(4));
   assert!(payload.inner().provenance().ptrs().is_empty());
   let scalar=payload.inner().read_scalar(&tcx,mir::interpret::alloc_range(Size::ZERO,Size::from_bytes(4)),false).unwrap();
   let returned=scalar.to_u32().report_err().unwrap();
   assert_eq!(u64::from(returned),u64::from(value)*(u64::from(value)+1)/2);
   let repeat=tcx.eval_to_allocation_raw(env.as_query_input(global)).unwrap();
   assert_eq!(repeat,result);
   let retry_env=ty::TypingEnv::new(env.param_env,ty::TypingMode::PostAnalysis);
   assert_eq!(tcx.eval_to_allocation_raw(retry_env.as_query_input(global)).unwrap(),result);
   let converted=tcx.eval_to_const_value_raw(env.as_query_input(global)).unwrap();
   let mir::ConstValue::Scalar(converted)=converted else {panic!("non-scalar query result")};
   assert_eq!(converted.to_u32().report_err().unwrap(),returned);
   println!("allocation-ok\t{name}\tinput={value}\tid={:?}\tvalue={returned}\timmutable=true\trelocations=0\trepeat-same-id=true\tpostanalysis-same-id=true\tvalue-provider-agrees=true",result.alloc_id);
   results.push((result,payload));
  }
  assert_ne!(results[0].0.alloc_id,results[1].0.alloc_id);
  assert_eq!(results[0].1,results[1].1);
  println!("source-identities\tdistinct-root-ids=true\tequal-memory=true");
  Compilation::Stop
 }
}
fn main(){rustc_driver::compiler_entrypoint(&std::env::args().collect::<Vec<_>>(),&mut Oracle)}
