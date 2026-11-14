#![feature(rustc_private)]
// Pinned independent instance-selection observations for the actual no_std
// Value/Cell runtime fixture's through(&mut dyn Value) argument. Shared exporter
// code encodes raw generic syntax only; try_resolve and expect_resolve_for_vtable
// are called here and their physical definitions/arguments/kinds/slots emitted.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_trait_selection;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::ty::{self,TyCtxt};
fn identity(def:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>)->String {
 args.iter().map(|arg|generic_material::argument(tcx,arg).expect("raw argument")).collect::<Vec<_>>().join(",")
}
fn instance<'tcx>(tcx:TyCtxt<'tcx>,value:ty::Instance<'tcx>)->String {
 let (kind,slot)=match value.def {
  ty::InstanceKind::Virtual(_,slot)=>("virtual",slot.to_string()),
  ty::InstanceKind::Item(_)=>("item","null".into()),
  ty::InstanceKind::Shim(ty::ShimKind::Reify(_,None))=>("reify_none","null".into()),
  ty::InstanceKind::Shim(ty::ShimKind::Reify(_,Some(ty::ReifyReason::Vtable)))=>("reify_vtable","null".into()),
  _=>panic!("uncovered object oracle instance {:?}",value.def),
 };
 format!("{{\"kind\":\"{}\",\"slot\":{},\"definition\":{},\"arguments\":[{}]}}",kind,slot,identity(value.def_id()),arguments(tcx,value.args))
}
struct Oracle;
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();let mut rows=Vec::new();
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)!=DefKind::Fn {continue;}
   let symbol=tcx.item_name(local.to_def_id());let name=symbol.as_str();if name != "through" {continue;}
   let sig=tcx.instantiate_bound_regions_with_erased(tcx.fn_sig(local).instantiate_identity().skip_norm_wip());
   let ty::Ref(_,object,_) = *sig.inputs()[0].kind() else {panic!("query reference")};
   let ty::Dynamic(predicates,_) = *object.kind() else {panic!("query dynamic")};
   let mut methods=Vec::new();
   if let Some(principal)=predicates.principal() {
    for inherited in rustc_trait_selection::traits::supertraits(tcx,principal.with_self_ty(tcx,object)) {
     let target=tcx.instantiate_bound_regions_with_erased(inherited);
     let base=tcx.first_method_vtable_slot(target);
     for method in tcx.own_existential_vtable_entries(target.def_id) {
      let generics=tcx.generics_of(*method);
      let args=tcx.mk_args_from_iter(target.args.iter().chain(generics.own_params.iter().map(|parameter|->ty::GenericArg<'tcx>{
       assert!(matches!(parameter.kind,ty::GenericParamDefKind::Lifetime));tcx.lifetimes.re_erased.into()
      })));
      let ordinary=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),*method,args).expect("selection error").expect("missing object instance");
      let reified=ty::Instance::expect_resolve_for_vtable(tcx,ty::TypingEnv::fully_monomorphized(),*method,args,tcx.def_span(*method));
      methods.push(format!("{{\"target\":{},\"target_arguments\":[{}],\"method\":{},\"arguments\":[{}],\"first_slot\":{},\"ordinary\":{},\"vtable\":{}}}",identity(target.def_id),arguments(tcx,target.args),identity(*method),arguments(tcx,args),base,instance(tcx,ordinary),instance(tcx,reified)));
     }
    }
   }
   rows.push(format!("{{\"name\":\"{}\",\"query_definition\":{},\"dynamic\":{},\"methods\":[{}]}}",name,identity(local.to_def_id()),generic_material::type_tree(tcx,object).expect("raw dyn syntax"),methods.join(",")));
  }
  println!("{{\"queries\":[{}]}}",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {let args=std::env::args().collect::<Vec<_>>();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
