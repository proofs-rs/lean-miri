#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::{mir, ty};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: ty::TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows = Vec::new();
        for definition in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(definition) != rustc_hir::def::DefKind::Fn ||
                tcx.item_name(definition.to_def_id()).as_str() != "root" { continue; }
            let body = tcx.instance_mir(ty::InstanceKind::Item(definition.to_def_id()));
            for block in body.basic_blocks.iter() {
                let mir::TerminatorKind::Call { func: mir::Operand::Constant(value), .. } =
                    &block.terminator().kind else { continue; };
                let function = tcx.erase_and_anonymize_regions(value.ty());
                let ty::FnDef(def, arguments) = function.kind() else { continue; };
                let expected = generic_material::type_tree(tcx, function).unwrap();
                let signature = tcx.fn_sig(*def).instantiate(tcx, arguments.skip_binder()).skip_norm_wip();
                rows.push(format!("{{\"expected\":{expected},\"argument_binders\":{},\"signature_binders\":{}}}",
                    arguments.bound_vars().len(), signature.bound_vars().len()));
            }
        }
        assert!(rows.len() >= 3, "fixture must contain three ordinary direct callees");
        println!("[{}]", rows.join(","));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args().collect();
    rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args, &mut Oracle))
}
