#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/generic_mir.rs"] mod generic_mir;
#[path="../exporter/src/generic_mir_call.rs"] mod generic_mir_call;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty::{self,TyCtxt}};

fn callees<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>)->Vec<String> {
    body.basic_blocks.iter().filter_map(|block|match &block.terminator().kind {
        mir::TerminatorKind::Call{func,..}=>Some(generic_mir_call::callee(tcx,func).unwrap()),
        _=>None,
    }).collect()
}
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows=Vec::new();
        let mut residuals=0;
        for def in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(def)!=rustc_hir::def::DefKind::Fn {continue}
            let name=tcx.item_name(def.to_def_id());
            let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
            if name.as_str().starts_with("ResidualDirect") {
                let mut calls=0;
                for block in body.basic_blocks.iter() {
                    if let mir::TerminatorKind::Call{func,..}=&block.terminator().kind {
                        assert!(generic_mir_call::callee(tcx,func).is_err());calls+=1;
                    }
                }
                assert!(calls>0);residuals+=1;continue;
            }
            if !name.as_str().starts_with("GenericDirect") {continue}
            let source=callees(tcx,body);
            assert_eq!(source.len(),1,"fixture must contain exactly one ordinary direct call");
            for replacement in [tcx.types.u8,tcx.types.u64,
                ty::Ty::new_imm_ref(tcx,tcx.lifetimes.re_static,tcx.types.u32)] {
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter()
                    .map(|_|->ty::GenericArg<'tcx>{replacement.into()}));
                let instance=ty::Instance{def:ty::InstanceKind::Item(def.to_def_id()),args};
                let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,
                    body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
                let expected=callees(tcx,&actual);
                let arguments=args.iter().map(|arg|generic_material::argument(tcx,arg).unwrap())
                    .collect::<Vec<_>>().join(",");
                rows.push(format!("{{\"source\":{},\"arguments\":[{arguments}],\"expected\":{}}}",source[0],expected[0]));
            }
        }
        assert_eq!(rows.len(),6);
        assert_eq!(residuals,2,"function pointers and trait methods remain explicit residuals");
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
