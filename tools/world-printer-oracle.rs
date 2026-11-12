#![feature(rustc_private)]
//! Test-only pinned Ty Display oracle for newly interned structural types.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{Ty,TyCtxt};
use rustc_hir::{def::DefKind,Mutability};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let definition=tcx.hir_crate_items(()).definitions().find(|def|
            tcx.def_kind(*def)==DefKind::Struct && tcx.item_name(def.to_def_id()).as_str()=="Novel")
            .expect("printer fixture nominal declaration absent").to_def_id();
        let nominal=tcx.type_of(definition).instantiate_identity().skip_norm_wip();
        let array=Ty::new_array(tcx,nominal,2);
        let types=[array,Ty::new_tup(tcx,&[nominal,tcx.types.u8]),Ty::new_tup(tcx,&[array]),
            Ty::new_ptr(tcx,array,Mutability::Mut),Ty::new_ptr(tcx,array,Mutability::Not),
            Ty::new_ref(tcx,tcx.lifetimes.re_erased,array,Mutability::Mut),
            Ty::new_ref(tcx,tcx.lifetimes.re_static,array,Mutability::Not),
            Ty::new_slice(tcx,nominal),Ty::new_tup(tcx,&[]),Ty::new_array(tcx,tcx.types.u8,0)];
        let rows=types.into_iter().map(|ty|format!("{{\"type\":{},\"display\":{:?}}}",
            generic_material::type_tree(tcx,ty).expect("typed printer oracle"),ty.to_string())).collect::<Vec<_>>();
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
