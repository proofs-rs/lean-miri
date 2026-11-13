#![feature(rustc_private)]
extern crate rustc_driver;extern crate rustc_hir;extern crate rustc_interface;extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};use rustc_hir::def::DefKind;use rustc_middle::{ty::{self,TyCtxt},traits::ImplSource};
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let env=ty::TypingEnv::fully_monomorphized();let mut matches=Vec::new();
  for local in tcx.hir_crate_items(()).definitions(){
   if tcx.def_kind(local)!=DefKind::Fn||tcx.item_name(local.to_def_id()).as_str()!="query_async"{continue;}
   for declaration in tcx.optimized_mir(local).local_decls.iter(){if let ty::CoroutineClosure(..)=*declaration.ty.kind(){if !matches.contains(&declaration.ty){matches.push(declaration.ty)}}}
  }
  assert_eq!(matches.len(),1);let self_ty=matches[0];let ty::CoroutineClosure(_,args)=*self_ty.kind() else{unreachable!()};
  let tuple=args.as_coroutine_closure().coroutine_closure_sig().skip_binder().tupled_inputs_ty;
  let args=tcx.mk_args(&[self_ty.into(),tuple.into()]);let parent=tcx.lang_items().fn_once_trait().unwrap();let output=tcx.lang_items().fn_once_output().unwrap();
  let reference=ty::TraitRef::new_from_args(tcx,parent,args);assert!(matches!(tcx.codegen_select_candidate(env.as_query_input(reference)),Ok(ImplSource::Builtin(..))));
  let projection=ty::Ty::new_projection(tcx,ty::IsRigid::No,output,args);let actual=tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(projection)).expect("actual async closure FnOnce Output");
  println!("{{\"self\":{},\"args_tuple\":{},\"fn_once\":{{\"crate\":{},\"index\":{}}},\"proven\":true,\"output\":{}}}",generic_material::type_tree(tcx,self_ty).unwrap(),generic_material::type_tree(tcx,tuple).unwrap(),parent.krate.as_u32(),parent.index.as_u32(),generic_material::type_tree(tcx,actual).unwrap());Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
