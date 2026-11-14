#![feature(rustc_private)]
extern crate rustc_driver; extern crate rustc_hir; extern crate rustc_interface; extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::def_id::{CrateNum,DefId,DefIndex};
use rustc_middle::{ty::{self,TyCtxt},traits::{ImplSource,CodegenObligationError}};
fn id(c:u32,i:u32)->DefId{DefId{krate:CrateNum::from_u32(c),index:DefIndex::from_u32(i)}}
fn identity(d:DefId)->String{format!("{{\"crate\":{},\"index\":{}}}",d.krate.as_u32(),d.index.as_u32())}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors(); let env=ty::TypingEnv::fully_monomorphized();
  let body=tcx.optimized_mir(id(1,9944));
  let self_ty=tcx.erase_and_anonymize_regions(body.local_decls[rustc_middle::mir::Local::from_u32(5)].ty);
  let ty::Ref(_,slice,mutability)=*self_ty.kind() else{panic!("physical caller local5 must be reference")};
  assert_eq!(mutability,rustc_hir::Mutability::Mut); assert!(matches!(slice.kind(),ty::Slice(_)));
  let args=tcx.mk_args(&[self_ty.into()]);
  let output=ty::Ty::new_projection(tcx,ty::IsRigid::No,id(2,10948),args);
  let normalized=tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(output)).expect("IntoIter normalization");
  let signature=tcx.try_normalize_erasing_regions(env,tcx.fn_sig(id(2,10949)).instantiate(tcx,args)).expect("std1257 signature");
  let mut rows=Vec::new();
  for (name,subject) in [("reference",self_ty),("slice",slice),("iterator",normalized)] {
    let reference=ty::TraitRef::new(tcx,id(2,11138),[subject]);
    let result=match tcx.codegen_select_candidate(env.as_query_input(reference)) {
      Ok(ImplSource::UserDefined(data))=>format!("{{\"kind\":\"implementation\",\"definition\":{}}}",identity(data.impl_def_id)),
      Err(CodegenObligationError::Unimplemented)=>"{\"kind\":\"no_solution\"}".into(),
      other=>panic!("uncovered actual Iterator selection {:?}",other)
    };
    rows.push(format!("{{\"name\":\"{}\",\"self\":{},\"result\":{}}}",name,generic_material::type_tree(tcx,subject).unwrap(),result));
  }
  println!("{{\"caller\":{},\"method\":{},\"self\":{},\"normalized_output\":{},\"normalized_signature\":{},\"iterator_goals\":[{}]}}",identity(id(1,9944)),identity(id(2,10949)),generic_material::type_tree(tcx,self_ty).unwrap(),generic_material::type_tree(tcx,normalized).unwrap(),generic_material::signature_tree(tcx,signature).unwrap(),rows.join(","));
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
