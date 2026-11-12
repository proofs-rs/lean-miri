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
            if !name.as_str().starts_with("GenericDirect") && !name.as_str().starts_with("ResidualDirect") {continue}
            let body=tcx.instance_mir(ty::InstanceKind::Item(def.to_def_id()));
            if name.as_str().starts_with("ResidualDirect") {
                let mut calls=0;
                for block in body.basic_blocks.iter() {
                    if let mir::TerminatorKind::Call{func,..}=&block.terminator().kind {
                        assert!(generic_mir_call::callee(tcx,func).is_err(),"residual callee accepted: {name} {func:?}");calls+=1;
                    }
                }
                assert!(calls>0);residuals+=1;continue;
            }
            if !name.as_str().starts_with("GenericDirect") {continue}
            let source=callees(tcx,body);
            assert_eq!(source.len(),1,"fixture must contain exactly one ordinary direct call");
            let replacements=[tcx.types.u8,tcx.types.u64,
                ty::Ty::new_imm_ref(tcx,tcx.lifetimes.re_static,tcx.types.u32)];
            for (case,&replacement) in replacements.iter().enumerate() {
                let args=tcx.mk_args_from_iter(tcx.generics_of(def).own_params.iter().enumerate()
                    .map(|(index,_)|->ty::GenericArg<'tcx>{
                        if index==0 {replacement.into()} else {replacements[(case+index)%replacements.len()].into()}
                    }));
                let instance=ty::Instance{def:ty::InstanceKind::Item(def.to_def_id()),args};
                let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,
                    body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
                let expected=callees(tcx,&actual);
                let dependencies=generic_mir_call::dependencies(tcx,body,args).unwrap();
                assert_eq!(dependencies.len(),1);
                for dependency in dependencies {
                    let ty::FnDef(def,target_args)=dependency.function_type.kind() else {panic!()};
                    let actual_instance=ty::Instance::try_resolve(tcx,ty::TypingEnv::fully_monomorphized(),
                        *def,target_args.skip_binder()).unwrap().unwrap();
                    assert_eq!(dependency.instance,actual_instance);
                    assert!(actual.basic_blocks.iter().any(|block|match &block.terminator().kind {
                        mir::TerminatorKind::Call{func:mir::Operand::Constant(value),..}=>
                            value.const_.ty()==dependency.function_type,
                        _=>false,
                    }));
                }
                let arguments=args.iter().map(|arg|generic_material::argument(tcx,arg).unwrap())
                    .collect::<Vec<_>>().join(",");
                rows.push(format!("{{\"source\":{},\"arguments\":[{arguments}],\"expected\":{}}}",source[0],expected[0]));
            }
        }
        let drop_glue=tcx.lang_items().get(rustc_attr_ir::LangItem::DropGlue).unwrap();
        let drop_operand=mir::Operand::function_handle(tcx,drop_glue,&[tcx.types.u32.into()],tcx.def_span(drop_glue));
        assert!(generic_mir_call::callee(tcx,&drop_operand).is_err(),"drop glue is not an ordinary Item");
        assert_eq!(rows.len(),6);
        assert_eq!(residuals,5,"function pointers and trait methods remain explicit residuals");
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
