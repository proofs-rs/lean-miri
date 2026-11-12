#![feature(rustc_private)]
//! Independent pinned-rustc declaration-variance oracle, never a producer seed.
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{self, TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows = Vec::new();
        for name in ["Co","Contra","Inv","Nested","Phantom","Cell","Rec","A","B",
            "Const","Lifetime","Projection","AliasCo","unused","identity"] {
            let def = tcx.hir_crate_items(()).definitions().find(|def|
                matches!(tcx.def_kind(*def), rustc_hir::def::DefKind::Struct |
                    rustc_hir::def::DefKind::Fn) && tcx.item_name(def.to_def_id()).as_str() == name)
                .expect("variance fixture declaration").to_def_id();
            let values = tcx.variances_of(def).iter().map(|variance| match variance {
                ty::Covariant => "\"covariant\"", ty::Contravariant => "\"contravariant\"",
                ty::Invariant => "\"invariant\"", ty::Bivariant => "\"bivariant\"",
            }).collect::<Vec<_>>().join(",");
            rows.push(format!("{{\"name\":\"{name}\",\"crate\":{},\"index\":{},\"variances\":[{values}]}}",
                def.krate.as_u32(),def.index.as_u32()));
        }
        println!("[{}]",rows.join(","));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args = std::env::args().collect::<Vec<_>>();
    rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args, &mut Oracle))
}
