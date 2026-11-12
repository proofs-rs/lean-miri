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
        let definitions: Vec<_> = tcx.hir_crate_items(()).definitions().filter(|&d|
            matches!(tcx.def_kind(d), rustc_hir::def::DefKind::TyAlias | rustc_hir::def::DefKind::Struct |
                rustc_hir::def::DefKind::Enum | rustc_hir::def::DefKind::Fn)).collect();
        let replacement = definitions.iter().find(|&&d| tcx.item_name(d.to_def_id()).as_str() == "Replacement")
            .map(|&d| tcx.type_of(d).instantiate_identity().skip_norm_wip()).unwrap();
        let region = ty::Region::new_bound(tcx, ty::DebruijnIndex::from_u32(0),
            ty::BoundRegion { var: ty::BoundVar::from_u32(0), kind: ty::BoundRegionKind::Anon });
        let reference = ty::Ty::new_imm_ref(tcx, region, tcx.types.u32);
        let constant = ty::Const::new_bound(tcx, ty::DebruijnIndex::from_u32(0),
            ty::BoundConst::new(ty::BoundVar::from_u32(0)));
        let mut rows = Vec::new();
        for definition in definitions {
            if !tcx.item_name(definition.to_def_id()).as_str().starts_with("Template") { continue; }
            let template = tcx.type_of(definition);
            let source_material=generic_material::definition_template(tcx,definition.to_def_id()).unwrap().unwrap();
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
                let signature_expected=if tcx.def_kind(definition)==rustc_hir::def::DefKind::Fn {
                    generic_material::signature_tree(tcx,tcx.fn_sig(definition).instantiate(tcx,args).skip_norm_wip()).unwrap()
                } else { "null".into() };
                let mut fields=Vec::new();
                if matches!(tcx.def_kind(definition),rustc_hir::def::DefKind::Struct|rustc_hir::def::DefKind::Enum) {
                    for (variant_index,variant) in tcx.adt_def(definition).variants().iter().enumerate() {
                        for (field_index,field) in variant.fields.iter().enumerate() {
                            let expected=generic_material::type_tree(tcx,field.ty(tcx,args).skip_norm_wip()).unwrap();
                            fields.push(format!("{{\"variant\":{variant_index},\"field\":{field_index},\"expected\":{expected}}}"));
                        }
                    }
                }
                rows.push(format!("{{\"source_material\":{source_material},\"template\":{material},\"arguments\":[{}],\"expected\":{result},\"signature_expected\":{signature_expected},\"field_expected\":[{}]}}",arguments.join(","),fields.join(",")));
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
