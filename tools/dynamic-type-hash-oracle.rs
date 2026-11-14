#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_data_structures;
extern crate rustc_hashes;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/type_hash_material.rs"] mod type_hash_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt,TypeVisitableExt};
use rustc_data_structures::stable_hash::{StableHash,StableHasher};
fn hash(tcx:TyCtxt<'_>,value:&impl StableHash)->u128 {tcx.with_stable_hashing_context(|mut hcx|{let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx|value.stable_hash(hcx,&mut h));h.finish::<rustc_hashes::Hash128>().as_u128()})}
struct Oracle;
impl Callbacks for Oracle{fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 let id=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="dynamic_hashes").unwrap();
 let signature=tcx.fn_sig(id).instantiate_identity().skip_norm_wip().skip_binder();
 let mut rows=Vec::new();
 for &ty in signature.inputs(){
  let ty::Ref(_,inner,_)=ty.kind()else{panic!("reference dyn input")};
  assert!(type_hash_material::eligible(*inner));
  let erased=tcx.erase_and_anonymize_regions(*inner);
  let ty::Dynamic(predicates,_)=erased.kind()else{panic!("expecteddynamic")};
  let mut definitions=Vec::new();
  for predicate in predicates.iter(){let id=predicate.def_id();definitions.push(format!("{{\"crate\":{},\"index\":{},\"hash\":\"{}\"}}",id.krate.as_u32(),id.index.as_u32(),u128::from_le_bytes(tcx.def_path_hash(id).0.to_le_bytes())));}
  rows.push(format!("{{\"display\":{:?},\"type\":{},\"anonymized\":{},\"predicates\":\"{}\",\"definitions\":[{}],\"has_erasable_regions\":{},\"is_monomorphic\":{},\"is_monomorphic_enough\":{},\"hash\":\"{}\"}}",format!("{inner:?}"),generic_material::type_tree(tcx,*inner).unwrap(),generic_material::type_tree(tcx,erased).unwrap(),hash(tcx,&&predicates[..]),definitions.join(","),inner.has_erasable_regions(),!inner.has_non_region_param() && !inner.has_escaping_bound_vars() && !inner.has_infer() && !inner.has_placeholders() && !inner.references_error(),!inner.has_param(),tcx.type_id_hash(*inner).as_u128()));
 }
 println!("[{}]",rows.join(","));Compilation::Stop
}}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
