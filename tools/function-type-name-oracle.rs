#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_const_eval;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{Ty,TyCtxt};
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let defs=tcx.hir_crate_items(()).definitions().map(|d|d.to_def_id()).collect::<Vec<_>>();
        let wrap=*defs.iter().find(|&&d|tcx.def_kind(d)==DefKind::Struct&&tcx.item_name(d).as_str()=="Wrap").unwrap();
        let novel=Ty::new_adt(tcx,tcx.adt_def(wrap),tcx.mk_args(&[tcx.types.u16.into()]));
        let mut types=Vec::new();
        for &definition in &defs {
            if tcx.def_kind(definition)!=DefKind::Fn {continue}
            let name=tcx.item_name(definition);
            if ["identity","unsafe_identity","feature_identity","noop"].contains(&name.as_str()) {
                types.push(Ty::new_fn_def(tcx,definition,rustc_middle::ty::Binder::dummy(tcx.mk_args(&[novel.into()]))));
            }
        }
        let rows=types.into_iter().map(|ty| {
            let rustc_middle::ty::FnDef(definition,_) = *ty.kind() else {unreachable!()};
            let header=tcx.hir_node_by_def_id(definition.expect_local()).fn_sig().unwrap().header.safety;
            let safety=match header {
                rustc_hir::HeaderSafety::Normal(rustc_hir::Safety::Safe)=>"normal_safe",
                rustc_hir::HeaderSafety::Normal(rustc_hir::Safety::Unsafe)=>"normal_unsafe",
                rustc_hir::HeaderSafety::SafeTargetFeatures=>"safe_target_features",
            };
            format!("{{\"type\":{},\"display\":{:?},\"intrinsic\":{:?},\"raw_header_safety\":{:?}}}",
                generic_material::type_tree(tcx,ty).unwrap(),ty.to_string(),rustc_const_eval::util::type_name(tcx,ty),safety)
        }).collect::<Vec<_>>();
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
