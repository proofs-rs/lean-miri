#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_data_structures;
extern crate rustc_hashes;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty::{self,TyCtxt}};
use rustc_data_structures::stable_hash::{StableHash,StableHasher};
fn hash(tcx:TyCtxt<'_>,value:&impl StableHash)->u128 {
 tcx.with_stable_hashing_context(|mut hcx| {let mut hasher=StableHasher::new(); hcx.while_hashing_spans(false,|hcx|value.stable_hash(hcx,&mut hasher));hasher.finish::<rustc_hashes::Hash128>().as_u128()})
}
fn row<'tcx>(tcx:TyCtxt<'tcx>,ty:ty::Ty<'tcx>,novel:bool)->String {
 let normalized=tcx.erase_and_anonymize_regions(ty);
 let ty::Closure(owner,args)=normalized.kind() else {panic!("closure oracle shape")};
 let actual=tcx.type_id_hash(ty).as_u128();
 let recomposed=tcx.with_stable_hashing_context(|mut hcx| {
  let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx| {
   17u8.stable_hash(hcx,&mut h);owner.stable_hash(hcx,&mut h);args.stable_hash(hcx,&mut h);
  });h.finish::<rustc_hashes::Hash128>().as_u128()
 });
 assert_eq!(actual,recomposed,"pinned Closure TyKind stable stream differs");
 let generics=tcx.generics_of(*owner);
 assert_eq!(generics.count(),args.len());
 assert_eq!(generics.parent_count+3,args.len());
 format!("{{\"display\":{:?},\"type\":{},\"anonymized\":{},\"hash\":\"{actual}\",\"definition_hash\":\"{}\",\"argument_hash\":\"{}\",\"parent_count\":{},\"argument_count\":{},\"signature_bound_variables\":{},\"kind\":{:?},\"novel\":{novel}}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),generic_material::type_tree(tcx,normalized).unwrap(),u128::from_le_bytes(tcx.def_path_hash(*owner).0.to_le_bytes()),hash(tcx,&&args[..]),generics.parent_count,args.len(),args.as_closure().sig().bound_vars().len(),format!("{:?}",args.as_closure().kind()))
}
fn closures<'tcx>(body:&mir::Body<'tcx>)->Vec<ty::Ty<'tcx>> {
 let mut result=Vec::new();for local in body.local_decls.iter(){if matches!(local.ty.kind(),ty::Closure(..)) && !result.contains(&local.ty){result.push(local.ty)}}result
}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let mut rows=Vec::new();
  let definition=tcx.hir_crate_items(()).definitions().find(|def|tcx.def_path_str(def.to_def_id())=="closure_hashes").unwrap().to_def_id();
  let body=tcx.instance_mir(ty::InstanceKind::Item(definition));
  let instance=ty::Instance{def:ty::InstanceKind::Item(definition),args:tcx.mk_args(&[])};
  let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
  for ty in closures(&actual){rows.push(row(tcx,ty,false));}
  let definition=tcx.hir_crate_items(()).definitions().find(|def|tcx.def_path_str(def.to_def_id())=="generic_hashes").unwrap().to_def_id();
  let body=tcx.instance_mir(ty::InstanceKind::Item(definition));
  for (ty,count,novel) in [(tcx.types.u16,3,false),(ty::Ty::new_array(tcx,tcx.types.u8,1979),97,true)] {
   let count=ty::Const::from_target_usize(tcx,count);
   let args=tcx.mk_args(&[tcx.lifetimes.re_static.into(),ty.into(),count.into()]);let instance=ty::Instance{def:ty::InstanceKind::Item(definition),args};
   let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
   for ty in closures(&actual){rows.push(row(tcx,ty,novel));}
  }
  assert_eq!(rows.len(),9,"expected seven local closures, one ordinary generic and one novel generic");
  println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
