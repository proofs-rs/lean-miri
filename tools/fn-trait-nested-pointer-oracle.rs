#![feature(rustc_private)]
extern crate rustc_driver;extern crate rustc_hir;extern crate rustc_interface;extern crate rustc_middle;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::{ty::{self,TyCtxt},traits::{ImplSource,CodegenObligationError}};
fn identity(d:DefId)->String{format!("{{\"crate\":{},\"index\":{}}}",d.krate.as_u32(),d.index.as_u32())}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let env=ty::TypingEnv::fully_monomorphized();let mut seen=std::collections::HashSet::new();let mut selves=Vec::new();
  for local in tcx.hir_crate_items(()).definitions(){
   if tcx.def_kind(local)!=DefKind::Fn || !tcx.item_name(local.to_def_id()).as_str().starts_with("query_"){continue;}
   let body=tcx.optimized_mir(local);
   for declaration in body.local_decls.iter(){
    let self_ty=declaration.ty;
    let accepted=match self_ty.kind(){ty::Closure(..)|ty::FnPtr(..)=>true,ty::FnDef(id,_)=>["plain","unsafe_plain","featured"].contains(&tcx.item_name(*id).as_str()),_=>false};
    if accepted&&seen.insert(self_ty){selves.push(self_ty);}
   }
  }
  let output_def=tcx.lang_items().fn_once_output().expect("Output");let mut rows=Vec::new();
  for self_ty in selves {
   let (family,sig,args_tuple,features)=match *self_ty.kind(){
    ty::Closure(_,args)=>{let sig=args.as_closure().sig();("closure",sig,sig.skip_binder().inputs()[0],"null".to_owned())},
    ty::FnPtr(..)=>{let sig=self_ty.unnormalized_fn_sig(tcx).skip_norm_wip();("fn_pointer",sig,ty::Ty::new_tup(tcx,sig.skip_binder().inputs()),"null".into())},
    ty::FnDef(id,_)=>{let sig=self_ty.unnormalized_fn_sig(tcx).skip_norm_wip();let features=tcx.codegen_fn_attrs(id).target_features.iter().map(|f|format!("\"{}\"",f.name.as_str())).collect::<Vec<_>>().join(",");("fn_definition",sig,ty::Ty::new_tup(tcx,sig.skip_binder().inputs()),format!("[{}]",features))},
    _=>unreachable!(),
   };
   let args=tcx.mk_args(&[self_ty.into(),args_tuple.into()]);let mut goals=Vec::new();
   for (name,id) in [("fn",tcx.lang_items().fn_trait().unwrap()),("fn_mut",tcx.lang_items().fn_mut_trait().unwrap()),("fn_once",tcx.lang_items().fn_once_trait().unwrap())]{
    let reference=ty::TraitRef::new_from_args(tcx,id,args);
    let proven=match tcx.codegen_select_candidate(env.as_query_input(reference)){Ok(ImplSource::Builtin(..))=>true,Err(CodegenObligationError::Unimplemented)=>false,other=>panic!("uncovered callable selection {:?}",other)};
    let output=if proven {let alias=ty::Ty::new_projection(tcx,ty::IsRigid::No,output_def,args);Some(tcx.try_normalize_erasing_regions(env,ty::Unnormalized::new_wip(alias)).expect("Output normalization"))}else{None};
    goals.push(format!("{{\"lang_item\":\"{}\",\"definition\":{},\"proven\":{},\"output\":{}}}",name,identity(id),proven,output.map(|t|generic_material::type_tree(tcx,t).unwrap()).unwrap_or("null".into())));
   }
   let inner=sig.skip_binder().inputs()[0];
   let unsafe_inner=ty::Ty::new_fn_ptr(tcx,inner.unnormalized_fn_sig(tcx).skip_norm_wip().map_bound(|sig|sig.set_safety(rustc_hir::Safety::Unsafe)));
   let wrong_tuple=ty::Ty::new_tup(tcx,&[unsafe_inner]);
   let wrong_args=tcx.mk_args(&[self_ty.into(),wrong_tuple.into()]);
   let wrong_ref=ty::TraitRef::new_from_args(tcx,tcx.lang_items().fn_once_trait().unwrap(),wrong_args);
   assert!(matches!(tcx.codegen_select_candidate(env.as_query_input(wrong_ref)),Err(CodegenObligationError::Unimplemented)));
   rows.push(format!("{{\"family\":\"{}\",\"self\":{},\"args_tuple\":{},\"wrong_args_tuple\":{},\"wrong_args_proven\":false,\"raw_signature\":{},\"raw_target_features\":{},\"output_definition\":{},\"goals\":[{}]}}",family,generic_material::type_tree(tcx,self_ty).unwrap(),generic_material::type_tree(tcx,args_tuple).unwrap(),generic_material::type_tree(tcx,wrong_tuple).unwrap(),generic_material::signature_tree(tcx,sig).unwrap(),features,identity(output_def),goals.join(",")));

  }
  println!("{{\"queries\":[{}]}}",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode{let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
