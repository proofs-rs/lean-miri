#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/type_hash_material.rs"] mod type_hash_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt,TypeVisitableExt};
struct Oracle;
impl Callbacks for Oracle{fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation{
 let id=tcx.hir_crate_items(()).definitions().find(|id|tcx.def_path_str(id.to_def_id())=="fn_pointer_hashes").unwrap();
 let signature=tcx.fn_sig(id).instantiate_identity().skip_norm_wip().skip_binder();
 let mut rows=Vec::new();
 for &root in signature.inputs(){
  for argument in root.walk(){
   let Some(ty)=argument.as_type()else{continue};
   if !matches!(ty.kind(),ty::FnPtr(..)) || !ty.has_escaping_bound_vars(){continue;}
   assert!(type_hash_material::eligible(ty),"producer excluded supported escaping syntax");
   rows.push(format!("{{\"display\":{:?},\"type\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),tcx.type_id_hash(ty).as_u128()));
  }
 }
 let named=signature.inputs().iter().flat_map(|ty|ty.walk()).filter_map(|arg|arg.as_region()).find_map(|r|match r.kind(){ty::ReBound(_,bound)if matches!(bound.kind,ty::BoundRegionKind::Named(_))=>Some(bound.kind),_=>None}).unwrap();
 let kinds=[ty::BoundRegionKind::Anon,ty::BoundRegionKind::NamedForPrinting(rustc_span::symbol::Symbol::intern("résumé'a")),ty::BoundRegionKind::ClosureEnv,named];
 for kind in kinds{
  let region=ty::Region::new_bound(tcx,ty::DebruijnIndex::from_u32(3),ty::BoundRegion{var:ty::BoundVar::from_u32(9),kind});
  let ty=ty::Ty::new_ref(tcx,region,tcx.types.u8,rustc_hir::Mutability::Not);
  assert!(type_hash_material::eligible(ty),"producer excluded supported escaping syntax");
   rows.push(format!("{{\"display\":{:?},\"type\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),tcx.type_id_hash(ty).as_u128()));
 }
 let region=ty::Region::new_canonical_bound(tcx,ty::BoundVar::from_u32(7));
 let ty=ty::Ty::new_ref(tcx,region,tcx.types.u8,rustc_hir::Mutability::Mut);
 assert!(type_hash_material::eligible(ty),"producer excluded supported escaping syntax");
   rows.push(format!("{{\"display\":{:?},\"type\":{},\"hash\":\"{}\"}}",format!("{ty:?}"),generic_material::type_tree(tcx,ty).unwrap(),tcx.type_id_hash(ty).as_u128()));
 assert!(!rows.is_empty(),"escaping FnPtr negative controls absent");
 println!("[{}]",rows.join(","));Compilation::Stop
}}
fn main(){let args=std::env::args().collect::<Vec<_>>();rustc_driver::compiler_entrypoint(&args,&mut Oracle);}
