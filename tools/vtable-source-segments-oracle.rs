#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_trait_selection;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_trait_selection::traits::vtable::{prepare_vtable_segments,VtblSegment};
use std::ops::ControlFlow;
fn reference<'tcx>(tcx:TyCtxt<'tcx>,value:ty::TraitRef<'tcx>)->String {
 let arguments=value.args.iter().map(|arg|generic_material::argument(tcx,arg).unwrap()).collect::<Vec<_>>().join(",");
 format!("{{\"definition\":{{\"crate\":{},\"index\":{}}},\"arguments\":[{arguments}]}}",value.def_id.krate.as_u32(),value.def_id.index.as_u32())
}
fn intern<'tcx>(nodes:&mut Vec<ty::TraitRef<'tcx>>,key:ty::TraitRef<'tcx>)->usize {
 if let Some(id)=nodes.iter().position(|&value|value==key){id}else{let id=nodes.len();nodes.push(key);id}
}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let mut rows=Vec::new();
  let mut pending=Vec::new();
  for name in ["A","B","C","D","Empty","EmptyDerived","EmptyLeft","Combo","Sparse","Multi","E","F","GenericRoot"] {
   let def=tcx.hir_crate_items(()).definitions().find(|def| matches!(tcx.def_kind(*def),rustc_hir::def::DefKind::Trait) && tcx.item_name(def.to_def_id()).as_str()==name).unwrap().to_def_id();
   pending.push(ty::TraitRef::new(tcx,def,[tcx.types.u8]));
  }
  let mut cursor=0;
  while cursor<pending.len() {
   let root=pending[cursor];let id=cursor;cursor+=1;
   let def=root.def_id;let name=tcx.item_name(def);
   let supers=tcx.explicit_super_clauses_of(def).iter_identity_copied().map(|raw|raw.skip_norm_wip()).filter_map(|(clause,_)|clause.instantiate_supertrait(tcx,ty::Binder::dummy(root)).as_trait_clause()).map(|clause|tcx.normalize_erasing_late_bound_regions(ty::TypingEnv::fully_monomorphized(),clause).trait_ref).collect::<Vec<_>>();
   let supers=supers.into_iter().map(|parent|intern(&mut pending,parent).to_string()).collect::<Vec<_>>();
   let own=!tcx.own_existential_vtable_entries(def).is_empty();
   let mut segments=Vec::new();
   let _:Option<()>=prepare_vtable_segments(tcx,root,|segment|{segments.push(match segment {VtblSegment::MetadataDSA=>"null".into(),VtblSegment::TraitOwnEntries{trait_ref,emit_vptr}=>format!("[{},{}]",intern(&mut pending,trait_ref),emit_vptr)});ControlFlow::Continue(())});
   rows.push(format!("{{\"name\":\"{name}\",\"id\":{},\"trait_ref\":{},\"supers\":[{}],\"own\":{own},\"segments\":[{}]}}",id,reference(tcx,root),supers.join(","),segments.join(",")));
  }
  println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
