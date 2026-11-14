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
use rustc_middle::ty::{self,TyCtxt};
use rustc_data_structures::stable_hash::{StableHash,StableHasher};
fn hash(tcx:TyCtxt<'_>,value:&impl StableHash)->u128 {tcx.with_stable_hashing_context(|mut hcx|{let mut h=StableHasher::new();hcx.while_hashing_spans(false,|hcx|value.stable_hash(hcx,&mut h));h.finish::<rustc_hashes::Hash128>().as_u128()})}
struct Oracle;
impl Callbacks for Oracle{fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 let id=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="fn_pointer_hashes").unwrap();
 let signature=tcx.fn_sig(id).instantiate_identity().skip_norm_wip().skip_binder();
 let mut rows=Vec::new();
 for &ty in signature.inputs(){
  assert!(type_hash_material::eligible(ty), "new FnPtr hash producer domain omitted");
  let erased=tcx.erase_and_anonymize_regions(ty);
  let ty::FnPtr(sig,header)=erased.kind()else{panic!("expectedfnptr")};
  rows.push(format!("{{\"display\":{:?},\"type\":{},\"anonymized\":{},\"type_list\":\"{}\",\"variables\":\"{}\",\"abi\":{},\"safe\":{},\"variadic\":{},\"splatted\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),generic_material::type_tree(tcx,erased).unwrap(),hash(tcx,&&sig.skip_binder().inputs_and_output[..]),hash(tcx,&&sig.bound_vars()[..]),header.abi().as_packed(),header.safety().is_safe(),header.c_variadic(),header.splatted().map(|n|n.to_string()).unwrap_or("null".into()),tcx.type_id_hash(ty).as_u128()));
 }
 let function=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="bound_function").unwrap().to_def_id();
 let region=ty::Region::new_bound(tcx,ty::DebruijnIndex::from_u32(0),ty::BoundRegion {var:ty::BoundVar::from_u32(0),kind:ty::BoundRegionKind::Anon});
 let args=tcx.mk_args(&[region.into()]);
 let binder=ty::Binder::bind_with_vars(args,tcx.mk_bound_variable_kinds(&[ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon)]));
 let ty=ty::Ty::new_fn_def(tcx,function,binder);
 assert!(type_hash_material::eligible(ty),"new FnDef binder producer domain omitted");
 rows.push(format!("{{\"display\":{:?},\"type\":{},\"anonymized\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),generic_material::type_tree(tcx,tcx.erase_and_anonymize_regions(ty)).unwrap(),tcx.type_id_hash(ty).as_u128()));
 println!("[{}]",rows.join(","));Compilation::Stop
}}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
