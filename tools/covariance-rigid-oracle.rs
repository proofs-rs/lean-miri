#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_const_eval;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let mut count = 0;
        for definition in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(definition) != rustc_hir::def::DefKind::Fn ||
                tcx.item_name(definition.to_def_id()).as_str() != "root" { continue; }
            let signature = tcx.fn_sig(definition).instantiate_identity().skip_norm_wip().skip_binder();
            let [source,target] = signature.inputs() else { panic!("expected two type inputs") };
            let environment = ty::TypingEnv::fully_monomorphized();
            let relate = |a,b| rustc_const_eval::util::relate_types(tcx,environment,ty::Variance::Covariant,a,b);
            assert!(!relate(*source,*target));
            assert!(!relate(*target,*source));
            assert!(relate(*source,*source));
            assert!(relate(*target,*target));
            println!("PASS rustc covariance rigid ADT/uint both directions false; exact identities true");
            count += 1;
        }
        assert_eq!(count,1);
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args().collect();
    rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args, &mut Oracle))
}
