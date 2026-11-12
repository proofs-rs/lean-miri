#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/generic_mir.rs"] mod generic_mir;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,TyCtxt};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows=Vec::new();
        let mut residual=0;
        for def in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(def)!=rustc_hir::def::DefKind::Fn {continue}
            let name=tcx.item_name(def.to_def_id());
            if name.as_str().starts_with("ResidualMir") {
                let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter().map(|_|->ty::GenericArg<'tcx>{tcx.types.u8.into()}));
                assert!(!generic_mir::eligible(body,args),"unsupported MIR source category was accepted");
                residual+=1;continue;
            }
            if !name.as_str().starts_with("GenericMir") {continue}
            let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
            let mut spans=std::collections::HashMap::new();
            let source=generic_mir::capture(tcx,body,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)}).unwrap();
            for replacement in [tcx.types.u8,tcx.types.u64] {
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter().map(|p|->ty::GenericArg<'tcx>{match p.kind {
                    ty::GenericParamDefKind::Type{..}=>replacement.into(),
                    ty::GenericParamDefKind::Lifetime=>tcx.lifetimes.re_erased.into(),
                    ty::GenericParamDefKind::Const{..}=>ty::Const::from_target_usize(tcx,3).into(),
                }}));
                assert!(generic_mir::eligible(body,args),"ported MIR category was not selected");
                let instance=ty::Instance{def:ty::InstanceKind::Item(def.to_def_id()),args};
                let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
                let expected=generic_mir::capture(tcx,&actual,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)}).unwrap();
                let arguments=args.iter().map(|a|generic_material::argument(tcx,a).unwrap()).collect::<Vec<_>>().join(",");
                rows.push(format!("{{\"source\":{source},\"arguments\":[{arguments}],\"expected\":{expected}}}"));
            }
        }
        assert!(rows.len()>=8,"fixture must exercise at least four generic MIR bodies");
        assert!(residual>=4,"fixture must exercise four unsupported source category controls");
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
