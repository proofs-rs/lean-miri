#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path = "../exporter/src/generic_material.rs"]
mod generic_material;
use rustc_middle::ty::{self, TyCtxt};
use rustc_driver::{Callbacks, Compilation};

struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self, _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let definitions: Vec<_> = tcx.hir_crate_items(()).definitions().filter(|&d| tcx.def_kind(d) == rustc_hir::def::DefKind::TyAlias).collect();
        let replacement = definitions.iter().find(|&&d| tcx.item_name(d.to_def_id()).as_str() == "Replacement")
            .map(|&d| tcx.type_of(d).instantiate_identity().skip_norm_wip()).unwrap();
        let region = ty::Region::new_bound(tcx, ty::DebruijnIndex::from_u32(0),
            ty::BoundRegion { var: ty::BoundVar::from_u32(0), kind: ty::BoundRegionKind::Anon });
        let reference = ty::Ty::new_imm_ref(tcx, region, tcx.types.u32);
        let constant = ty::Const::new_bound(tcx, ty::DebruijnIndex::from_u32(0),
            ty::BoundConst::new(ty::BoundVar::from_u32(0)));
        let mut rows = Vec::new();
        for definition in definitions {
            if tcx.def_kind(definition) != rustc_hir::def::DefKind::TyAlias { continue; }
            if !tcx.item_name(definition.to_def_id()).as_str().starts_with("Template") { continue; }
            let template = tcx.type_of(definition);
            for type_argument in [reference, replacement] {
                let args: ty::GenericArgsRef<'tcx> = tcx.mk_args_from_iter(tcx.generics_of(definition).own_params.iter().map(|p| -> ty::GenericArg<'tcx> {
                    match p.kind {
                        ty::GenericParamDefKind::Lifetime => region.into(),
                        ty::GenericParamDefKind::Type { .. } => type_argument.into(),
                        ty::GenericParamDefKind::Const { .. } => constant.into(),
                    }}));
                let material = generic_material::type_tree(tcx,template.instantiate_identity().skip_norm_wip()).unwrap();
                let arguments: Vec<_> = args.iter().map(|a|generic_material::argument(tcx,a).unwrap()).collect();
                let result = generic_material::type_tree(tcx,template.instantiate(tcx,args).skip_norm_wip()).unwrap();
                rows.push(format!("{{\"template\":{material},\"arguments\":[{}],\"expected\":{result}}}",arguments.join(",")));
            }
        }
        assert!(rows.len() >= 10, "fixture needs at least five generic templates");
        println!("[{}]",rows.join(","));
        Compilation::Stop
    }
}
fn main() -> std::process::ExitCode {
    let args: Vec<_> = std::env::args().collect();
    let status = rustc_driver::catch_with_exit_code(|| rustc_driver::compiler_entrypoint(&args,&mut Oracle));
    status
}
