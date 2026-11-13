//! Independent pinned instance selection and complete raw/normalized caller MIR.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/generic_mir.rs"] mod generic_mir;
#[path="../exporter/src/generic_mir_call.rs"] mod generic_mir_call;
use rustc_middle::{mir,ty};
use rustc_driver::{Callbacks,Compilation};
struct Inspector;
impl Callbacks for Inspector {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let definition=tcx.hir_crate_items(()).definitions().find(|d|
   tcx.def_kind(d.to_def_id())==rustc_hir::def::DefKind::Fn && tcx.item_name(d.to_def_id()).as_str()=="dispatch").unwrap();
  let body=tcx.optimized_mir(definition);
  let args=tcx.mk_args(&[tcx.types.u8.into()]);
  let dependencies=generic_mir_call::dependencies(tcx,body,args).unwrap();
  assert_eq!(dependencies.len(),1);
  assert!(dependencies[0].instance.is_none(),"trait declaration must not become Item(traitDef)");
  let ty::FnDef(trait_method,callee_args)=dependencies[0].function_type.kind() else {panic!("not FnDef")};
  assert!(tcx.trait_of_assoc(*trait_method).is_some());
  let selected=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),*trait_method,callee_args.skip_binder()).unwrap().unwrap();
  assert_ne!(selected.def.def_id(),*trait_method);
  let instance=ty::Instance{def:ty::InstanceKind::Item(definition.to_def_id()),args};
  let normalized=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
  let mut spans=std::collections::HashMap::new();
  let source=generic_mir::capture_extended(tcx,body,|span|{let n=spans.len() as u64;*spans.entry(span).or_insert(n)}).unwrap();
  let expected=generic_mir::capture_extended(tcx,&normalized,|span|{let n=spans.len() as u64;*spans.entry(span).or_insert(n)}).unwrap();
  let ty::InstanceKind::Item(selected_definition)=selected.def else {panic!("expected ordinary concrete impl Item")};
  let selected_body=tcx.optimized_mir(selected_definition);
  let selected_normalized=selected.try_instantiate_mir_and_normalize_erasing_regions(tcx,selected_body.typing_env(tcx),ty::EarlyBinder::bind(tcx,selected_body.clone())).unwrap();
  let selected_source=generic_mir::capture_extended(tcx,selected_body,|span|{let n=spans.len() as u64;*spans.entry(span).or_insert(n)}).unwrap();
  let selected_expected=generic_mir::capture_extended(tcx,&selected_normalized,|span|{let n=spans.len() as u64;*spans.entry(span).or_insert(n)}).unwrap();
  let call=body.basic_blocks.iter().find_map(|b|match &b.terminator().kind {mir::TerminatorKind::Call{func,..}=>Some(func.clone()),_=>None}).unwrap();
  let mut annotated=call.clone();
  let mir::Operand::Constant(value)=&mut annotated else {panic!("not constant")};
  value.user_ty=Some(ty::UserTypeAnnotationIndex::from_u32(0));
  assert_eq!(generic_mir_call::callee(tcx,&annotated).unwrap_err(),"direct source call requires absent user type annotation");
  assert!(generic_mir_call::callee(tcx,&mir::Operand::Copy(mir::Place::from(mir::RETURN_PLACE))).is_err());
  let mut locations=spans.into_iter().collect::<Vec<_>>();locations.sort_by_key(|(_,index)|*index);
  let locations=locations.into_iter().map(|(span,_)|format!("{{\"lo\":{},\"hi\":{},\"ctxt\":{:?}}}",span.lo().0,span.hi().0,format!("{:?}",span.ctxt()))).collect::<Vec<_>>().join(",");
  println!("{{\"name\":\"dispatch\",\"source_role\":\"runtime\",\"source\":{source},\"expected\":{expected},\"selected_source\":{selected_source},\"selected_expected\":{selected_expected},\"arguments\":[{}],\"spans\":[{locations}],\"trait_method\":{{\"crate\":{},\"index\":{}}},\"selected_method\":{{\"crate\":{},\"index\":{}}},\"physical_owner\":{{\"crate\":{},\"index\":{}}},\"negative_controls\":2}}",generic_material::type_tree(tcx,tcx.types.u8).unwrap(),trait_method.krate.as_u32(),trait_method.index.as_u32(),selected.def.def_id().krate.as_u32(),selected.def.def_id().index.as_u32(),definition.to_def_id().krate.as_u32(),definition.to_def_id().index.as_u32());
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode {
 let args=std::env::args().collect::<Vec<_>>();
 rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Inspector))
}
