#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_interface;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let def=tcx.hir_crate_items(()).definitions().find(|&def|tcx.def_kind(def)==DefKind::Fn && tcx.item_name(def.to_def_id()).as_str()=="echo").expect("echo source absent").to_def_id();
        let rows=[tcx.types.u16,tcx.types.u32,tcx.types.u128].iter().copied().map(|ty|{
            let instance=ty::Instance::new_raw(def,tcx.mk_args(&[ty.into()]));
            format!("{{\"definition\":{{\"crate\":{},\"index\":{}}},\"argument\":{},\"display\":{:?}}}",def.krate.as_u32(),def.index.as_u32(),generic_material::type_tree(tcx,ty).expect("raw type"),instance.to_string())
        }).collect::<Vec<_>>();
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
