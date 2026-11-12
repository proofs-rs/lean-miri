#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_const_eval;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::TyCtxt;
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let rows=tcx.hir_crate_items(()).definitions().filter(|&def|tcx.def_kind(def)==DefKind::TyAlias).map(|def| {
            let ty=tcx.type_of(def).instantiate_identity().skip_norm_wip();
            format!("{{\"type\":{},\"display\":{:?},\"intrinsic\":{:?}}}",generic_material::type_tree(tcx,ty).expect("raw FnPtr syntax"),ty.to_string(),rustc_const_eval::util::type_name(tcx,ty))
        }).collect::<Vec<_>>();
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
