#![feature(rustc_private)]
//! Independent finite oracle for the raw structural relation fragment.
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_const_eval;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{self, TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let env = ty::TypingEnv::fully_monomorphized();
        let types = (0..16).map(|index| {
            let name = format!("C{index}");
            let def = tcx.hir_crate_items(()).definitions().find(|def|
                tcx.def_kind(*def) == rustc_hir::def::DefKind::TyAlias &&
                tcx.item_name(def.to_def_id()).as_str() == name).expect("fixture alias");
            tcx.try_normalize_erasing_regions(env, tcx.type_of(def).instantiate_identity())
                .expect("fixture normalization")
        }).collect::<Vec<_>>();
        let mut rows = Vec::new();
        for (left,a) in types.iter().enumerate() {
            for (right,b) in types.iter().enumerate() {
                let value = rustc_const_eval::util::relate_types(tcx, env,
                    ty::Variance::Covariant, *a, *b);
                rows.push(format!("{{\"left\":{left},\"right\":{right},\"value\":{value}}}"));
            }
        }
        println!("[{}]", rows.join(","));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args = std::env::args().collect::<Vec<_>>();
    rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args, &mut Oracle))
}
