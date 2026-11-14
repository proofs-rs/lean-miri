#![feature(rustc_private)]
//! Independent obligation fulfillment, including genuine forall/static failures.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_infer;
extern crate rustc_trait_selection;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::ty::{self,TyCtxt};
fn identity(def:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>)->String {
    args.iter().map(|arg|generic_material::argument(tcx,arg).expect("raw argument"))
        .collect::<Vec<_>>().join(",")
}
fn reference<'tcx>(tcx:TyCtxt<'tcx>,value:ty::TraitRef<'tcx>)->String {
    format!("{{\"definition\":{},\"arguments\":[{}]}}",identity(value.def_id),arguments(tcx,value.args))
}
struct Oracle;
fn parameters(tcx:TyCtxt<'_>, definition:DefId)->String {
 let generics=tcx.generics_of(definition);
 (0..generics.count()).map(|index| match generics.param_at(index,tcx).kind {
 ty::GenericParamDefKind::Lifetime=>"\"region\"",ty::GenericParamDefKind::Type{..}=>"\"type\"",
 ty::GenericParamDefKind::Const{..}=>"\"constant\""}).collect::<Vec<_>>().join(",")
}
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let definition=tcx.hir_crate_items(()).definitions().find(|def|tcx.def_kind(*def)==DefKind::Trait&&tcx.item_name(def.to_def_id()).as_str()=="Shape").unwrap().to_def_id();
  let mut methods=Vec::new();
  for item in tcx.associated_items(definition).in_definition_order().filter(|item|item.is_fn()) {
   let signature=generic_material::signature_tree(tcx,tcx.fn_sig(item.def_id).instantiate_identity().skip_norm_wip()).unwrap();
   let mut clauses=Vec::new();
   for &(clause,_) in tcx.explicit_clauses_of(item.def_id).clauses {
    let variables=clause.kind().bound_vars().iter().map(generic_material::bound_variable).collect::<Vec<_>>().join(",");
    let predicate=match clause.kind().skip_binder() {
      ty::ClauseKind::Trait(goal)=>format!("{{\"kind\":\"trait\",\"polarity\":\"positive\",\"trait_ref\":{}}}",reference(tcx,goal.trait_ref)),
      ty::ClauseKind::TypeOutlives(value)=>format!("{{\"kind\":\"type_outlives\",\"type\":{},\"region\":{}}}",generic_material::type_tree(tcx,value.0).unwrap(),generic_material::region_tree(value.1).unwrap()),
      _=>panic!("unsupported scratch clause"),
    };
    clauses.push(format!("{{\"variables\":[{variables}],\"predicate\":{predicate}}}"));
   }
   methods.push(format!("{{\"definition\":{},\"name\":\"{}\",\"is_method\":{},\"is_final\":{},\"parameters\":[{}],\"parent_parameter_count\":{},\"signature\":{},\"own_clauses\":[{}]}}",identity(item.def_id),tcx.item_name(item.def_id),item.is_method(),item.defaultness(tcx).is_final(),parameters(tcx,item.def_id),tcx.generics_of(item.def_id).parent_count,signature,clauses.join(",")));
  }
  let entries=tcx.own_existential_vtable_entries(definition).iter().map(|def|identity(*def)).collect::<Vec<_>>().join(",");
  println!("{{\"source_methods\":[{}],\"oracle_own_entries\":[{entries}]}}",methods.join(","));
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode {
 let args=std::env::args().collect::<Vec<_>>();
 rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
