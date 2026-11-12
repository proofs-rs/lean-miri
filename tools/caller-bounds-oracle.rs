#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows=Vec::new();
        let leaf=tcx.hir_crate_items(()).definitions().find(|def|
            tcx.def_kind(*def)==rustc_hir::def::DefKind::Trait&&tcx.item_name(def.to_def_id()).as_str()=="Leaf").unwrap().to_def_id();
        for name in ["Positive","Missing"] {
            let definition=tcx.hir_crate_items(()).definitions().find(|def|
                tcx.def_kind(*def)==rustc_hir::def::DefKind::Struct&&tcx.item_name(def.to_def_id()).as_str()==name)
                .expect("fixture declaration").to_def_id();
            let args=ty::GenericArgs::identity_for_item(tcx,definition);
            let parameter=args.type_at(0);
            let goal=ty::TraitRef::new(tcx,leaf,[parameter]);
            let actual=match tcx.codegen_select_candidate(ty::TypingEnv::post_analysis(tcx,definition).as_query_input(goal)) {
              Ok(rustc_middle::traits::ImplSource::Param(_))=>"parameter",
              Err(rustc_middle::traits::CodegenObligationError::Unimplemented)=>"no_solution",
              other=>panic!("unexpected caller-bound selection {other:?}"),
            };
            rows.push(format!("{{\"definition\":{{\"crate\":{},\"index\":{}}},\"trait_definition\":{{\"crate\":{},\"index\":{}}},\"parameter\":{},\"expected\":\"{actual}\"}}",
                definition.krate.as_u32(),definition.index.as_u32(),leaf.krate.as_u32(),leaf.index.as_u32(),generic_material::type_tree(tcx,parameter).expect("raw parameter")));
        }
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {let args:Vec<_>=std::env::args().collect();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
