#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
#[path="../exporter/src/generic_mir.rs"] mod generic_mir;
#[path="../exporter/src/generic_mir_call.rs"] mod generic_mir_call;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty::{self,TyCtxt}};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows=Vec::new();
        let mut residual=0;
        let mut direct_family=false;
        for def in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(def)!=rustc_hir::def::DefKind::Fn {continue}
            let name=tcx.item_name(def.to_def_id());
            if name.as_str().starts_with("ResidualMir") || name.as_str().starts_with("ResidualDirect") {
                let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter().map(|_|->ty::GenericArg<'tcx>{tcx.types.u8.into()}));
                assert!(!generic_mir::eligible(tcx,body,args),"unsupported MIR source category was accepted");
                residual+=1;continue;
            }
            if !name.as_str().starts_with("GenericMir") && !name.as_str().starts_with("GenericDirect") {continue}
            direct_family |= name.as_str().starts_with("GenericDirect");
            let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
            let mut spans=std::collections::HashMap::new();
            let source=generic_mir::capture(tcx,body,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)}).unwrap();
            let replacements=[tcx.types.u8,tcx.types.u32,tcx.types.u64,
                ty::Ty::new_imm_ref(tcx,tcx.lifetimes.re_static,tcx.types.u32)];
            for (case,&replacement) in replacements.iter().enumerate() {
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter().enumerate().map(|(index,p)|->ty::GenericArg<'tcx>{match p.kind {
                    ty::GenericParamDefKind::Type{..}=>
                        if index==0 {replacement.into()} else {replacements[(case+index)%replacements.len()].into()},
                    ty::GenericParamDefKind::Lifetime=>tcx.lifetimes.re_erased.into(),
                    ty::GenericParamDefKind::Const{..}=>ty::Const::from_target_usize(tcx,3).into(),
                }}));
                if !direct_family {
                    assert!(generic_mir::eligible(tcx,body,args),"ported MIR category was not selected");
                }
                let instance=ty::Instance{def:ty::InstanceKind::Item(def.to_def_id()),args};
                let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
                let interface=generic_mir::interface(tcx,body,args).unwrap();
                assert_eq!(interface.argument_count,actual.arg_count);
                assert_eq!(interface.spread_argument,actual.spread_arg);
                assert_eq!(interface.return_type,actual.local_decls[mir::RETURN_PLACE].ty);
                for (local,ty) in interface.arguments {assert_eq!(ty,actual.local_decls[local].ty);}
                let expected=generic_mir::capture(tcx,&actual,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)}).unwrap();
                let arguments=args.iter().map(|a|generic_material::argument(tcx,a).unwrap()).collect::<Vec<_>>().join(",");
                rows.push(format!("{{\"source\":{source},\"arguments\":[{arguments}],\"expected\":{expected}}}"));
            }
        }
        if direct_family {assert_eq!(rows.len(),8);assert_eq!(residual,5);}
        else {assert!(rows.len()>=16);assert!(residual>=4);}
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
