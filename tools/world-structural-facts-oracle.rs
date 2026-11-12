#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,Ty,TyCtxt};
use rustc_hir::{def::DefKind,Mutability};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let find=|name:&str|tcx.hir_crate_items(()).definitions().find(|def|
            matches!(tcx.def_kind(*def),DefKind::Struct|DefKind::Enum|DefKind::Union)
            &&tcx.item_name(def.to_def_id()).as_str()==name).expect("fixture declaration absent").to_def_id();
        let adt=|name,arg:Ty<'tcx>|Ty::new_adt(tcx,tcx.adt_def(find(name)),tcx.mk_args(&[arg.into()]));
        let dropper=Ty::new_adt(tcx,tcx.adt_def(find("Dropper")),tcx.mk_args(&[]));
        let loop_ty=Ty::new_adt(tcx,tcx.adt_def(find("RefLoop")),tcx.mk_args(&[tcx.lifetimes.re_erased.into()]));
        let never=tcx.types.never;
        let ref_never=adt("RefWrap",never);
        let types=[adt("Wrap",never),adt("Wrap",dropper),adt("Either",never),adt("Only",never),
            adt("Union",dropper),adt("Wrap",loop_ty),ref_never,
            Ty::new_array(tcx,ref_never,0),Ty::new_array(tcx,ref_never,2),
            Ty::new_array(tcx,adt("Wrap",dropper),0),
            Ty::new_ptr(tcx,never,Mutability::Mut),Ty::new_ref(tcx,tcx.lifetimes.re_erased,never,Mutability::Mut)];
        let env=ty::TypingEnv::fully_monomorphized();
        let rows=types.into_iter().map(|ty|format!("{{\"type\":{},\"is_sized\":{},\"needs_drop\":{},\"opsem_inhabited\":{},\"display\":{}}}",
            generic_material::type_tree(tcx,ty).expect("typed world fact oracle"),ty.is_sized(tcx,env),
            ty.needs_drop(tcx,env),ty.is_opsem_inhabited(tcx,env),format!("{:?}",ty.to_string()))).collect::<Vec<_>>();
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
