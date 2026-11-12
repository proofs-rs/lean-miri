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
        for name in ["Direct","Inherited","Maybe"] {
            let definition=tcx.hir_crate_items(()).definitions().find(|def|
                tcx.def_kind(*def)==rustc_hir::def::DefKind::Struct&&tcx.item_name(def.to_def_id()).as_str()==name)
                .expect("fixture declaration").to_def_id();
            let args=ty::GenericArgs::identity_for_item(tcx,definition);
            let parameter=args.type_at(0);
            let actual=parameter.is_sized(tcx,ty::TypingEnv::post_analysis(tcx,definition));
            rows.push(format!("{{\"definition\":{{\"crate\":{},\"index\":{}}},\"parameter\":{},\"sized\":{actual}}}",
                definition.krate.as_u32(),definition.index.as_u32(),generic_material::type_tree(tcx,parameter).expect("raw parameter")));
        }
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {let args:Vec<_>=std::env::args().collect();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
