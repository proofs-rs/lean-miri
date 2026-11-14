#![feature(rustc_private)]
extern crate rustc_driver;extern crate rustc_hir;extern crate rustc_interface;extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};use rustc_hir::def_id::{CrateNum,DefId,DefIndex};use rustc_middle::ty::{self,TyCtxt};
fn identity(d:DefId)->String{format!("{{\"crate\":{},\"index\":{}}}",d.krate.as_u32(),d.index.as_u32())}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let env=ty::TypingEnv::fully_monomorphized();
  let krate=std::env::var("STD_CLOSURE_CRATE").unwrap().parse().unwrap();let index=std::env::var("STD_CLOSURE_INDEX").unwrap().parse().unwrap();
  let closure_def=DefId{krate:CrateNum::from_u32(krate),index:DefIndex::from_u32(index)};
  let body=tcx.optimized_mir(tcx.parent(closure_def));let mut matches=Vec::new();
  for declaration in body.local_decls.iter(){if let ty::Closure(id,_)=*declaration.ty.kind(){if id==closure_def{let ty=tcx.erase_and_anonymize_regions(declaration.ty);if !matches.contains(&ty){matches.push(ty);}}}}
  assert_eq!(matches.len(),1,"exact external parent MIR closure type");let closure=matches[0];
  let fn_once=tcx.lang_items().fn_once_trait().unwrap();let output=tcx.lang_items().fn_once_output().unwrap();
  let method=tcx.associated_items(fn_once).in_definition_order().find(|item|item.is_fn()).unwrap().def_id;
  let args=tcx.mk_args(&[closure.into(),tcx.types.unit.into()]);
  let projection=ty::Ty::new_projection(tcx,ty::IsRigid::No,output,args);
  let normalized_output=tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(projection)).expect("actual std closure Output");
  let raw=tcx.fn_sig(method).instantiate(tcx,args);
  let normalized=tcx.try_normalize_erasing_regions(env,raw).expect("actual std original FnOnce signature");
  println!("{{\"method_definition\":{},\"output_definition\":{},\"self\":{},\"normalized_output\":{},\"normalized_signature\":{}}}",identity(method),identity(output),generic_material::type_tree(tcx,closure).unwrap(),generic_material::type_tree(tcx,normalized_output).unwrap(),generic_material::signature_tree(tcx,normalized).unwrap());Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
