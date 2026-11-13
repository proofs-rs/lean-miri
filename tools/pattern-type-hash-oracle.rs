#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_data_structures;
extern crate rustc_hashes;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/type_hash_material.rs"] mod type_hash_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_data_structures::stable_hash::{StableHash,StableHasher};
fn hash(tcx:TyCtxt<'_>,value:&impl StableHash)->u128 {tcx.with_stable_hashing_context(|mut hcx|{let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx|value.stable_hash(hcx,&mut h));h.finish::<rustc_hashes::Hash128>().as_u128()})}
struct Oracle;
impl Callbacks for Oracle{fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 let id=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="pattern_layouts").unwrap();
 let signature=tcx.fn_sig(id).instantiate_identity().skip_norm_wip().skip_binder();
 let root=tcx.normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(),ty::Unnormalized::new_wip(signature.inputs()[0]));
 let ty::Tuple(types)=root.kind()else{panic!("expected pattern tuple")};
 let mut rows=Vec::new();
 for ty in types.iter(){
  let ty::Pat(_,pattern)=ty.kind()else{panic!("expected normalized Pat: {ty:?}")};
  assert!(type_hash_material::eligible(ty),"raw Pattern producer domain excluded actual key");
  rows.push(format!("{{\"display\":{:?},\"type\":{},\"pattern_hash\":\"{}\",\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),hash(tcx,pattern),tcx.type_id_hash(ty).as_u128()));
 }
 assert_eq!(rows.len(),7);
 println!("[{}]",rows.join(","));Compilation::Stop
}}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
