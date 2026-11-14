#![feature(rustc_private)]
//! Independent raw/normalized syntax, flags and printer oracle.
extern crate rustc_driver;
extern crate rustc_middle;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_const_eval;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let rows = tcx.hir_crate_items(()).definitions()
            .filter(|&def|tcx.def_kind(def) == DefKind::TyAlias).map(|def| {
            let ty = tcx.type_of(def).instantiate_identity().skip_norm_wip();
            let normalized = tcx.erase_and_anonymize_regions(ty);
            format!("{{\"type\":{},\"display\":{:?},\"intrinsic\":{:?},\"normalized\":{},\"normalized_display\":{:?},\"normalized_intrinsic\":{:?},\"has_erasable_regions\":{},\"is_monomorphic\":{},\"is_monomorphic_enough\":{}}}",
                generic_material::type_tree(tcx, ty).expect("raw FnPtr"), ty.to_string(),
                rustc_const_eval::util::type_name(tcx, ty),
                generic_material::type_tree(tcx, normalized).expect("normalized FnPtr"),
                normalized.to_string(), rustc_const_eval::util::type_name(tcx, normalized),
                ty.has_erasable_regions(), !ty.has_non_region_param() && !ty.has_escaping_bound_vars()
                    && !ty.has_infer() && !ty.has_placeholders() && !ty.references_error(),
                !ty.has_param())
        }).collect::<Vec<_>>();
        println!("[{}]", rows.join(","));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args = std::env::args().collect::<Vec<_>>();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args, &mut Oracle))
}
