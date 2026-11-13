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
  let mut rows=Vec::new();
  for local in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(local)!=DefKind::Fn { continue; }
   let symbol=tcx.item_name(local.to_def_id()); let name=symbol.as_str();
   if !name.starts_with("query_") { continue; }
   let sig=tcx.fn_sig(local).instantiate_identity().skip_norm_wip().skip_binder();
   let ty::Ref(_,concrete,_) = *sig.inputs()[0].kind() else {panic!("query ref")};
   let trait_ref=ty::TraitRef::new(tcx,definition,[ty::GenericArg::from(concrete),ty::GenericArg::from(tcx.lifetimes.re_static),ty::GenericArg::from(tcx.types.u8)]);
   let mut entries=Vec::new();
   for entry in tcx.vtable_entries(trait_ref) {
    let text=match entry {
      ty::VtblEntry::Method(instance)=> {
        let kind=match instance.def {
          ty::InstanceKind::Item(_)=>"selected",
          ty::InstanceKind::Shim(ty::ShimKind::VTable(_))=>"by_value_shim",
          _=>panic!("unsupported independent oracle kind {:?}",instance.def),
        };
        format!("{{\"kind\":\"{}\",\"definition\":{},\"arguments\":[{}]}}",kind,identity(instance.def_id()),arguments(tcx,instance.args))
      },
      ty::VtblEntry::Vacant=>"{\"kind\":\"vacant\"}".into(),
      _=>continue,
    };
    entries.push(text);
   }
   rows.push(format!("{{\"name\":\"{}\",\"reference\":{},\"entries\":[{}]}}",name,reference(tcx,trait_ref),entries.join(",")));
  }
  println!("{{\"queries\":[{}]}}",rows.join(","));
  Compilation::Stop
 }
}
fn main()->std::process::ExitCode {
 let args=std::env::args().collect::<Vec<_>>();
 rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
