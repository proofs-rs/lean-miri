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
use rustc_middle::ty;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let mut rows=Vec::new();
        let mut owners=Vec::new();
        for def in tcx.hir_crate_items(()).definitions() {
            if tcx.def_kind(def)!=rustc_hir::def::DefKind::Fn {continue}
            let body=tcx.optimized_mir(def);
            for block in body.basic_blocks.iter() {
                for statement in &block.statements {
                    let rustc_middle::mir::StatementKind::Assign(pair)=&statement.kind else {continue};
                    let rustc_middle::mir::Rvalue::Aggregate(kind,_)=&pair.1 else {continue};
                    let rustc_middle::mir::AggregateKind::Coroutine(owner,args)=&**kind else {continue};
                    if !owners.iter().any(|(seen,_)|seen==owner) {owners.push((*owner,*args));}
                }
            }
        }
        for (owner,args) in owners {
            let raw=ty::Ty::new_coroutine(tcx,owner,args);
            let body=tcx.optimized_mir(owner);
            let mut spans=std::collections::HashMap::new();
            let source=generic_mir::capture(tcx,body,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)})
                .unwrap_or_else(|error|panic!("actual coroutine source {}: {error}",tcx.def_path_str(owner)));
            for replacement in [tcx.types.u8,tcx.types.u64,tcx.types.bool,tcx.types.i128] {
                let parent=tcx.mk_args(&[replacement.into()]);
                let closed=ty::EarlyBinder::bind(tcx,raw).instantiate(tcx,parent).skip_normalization();
                let ty::Coroutine(_,args)=*closed.kind() else {unreachable!()};
                assert!(generic_mir::eligible(tcx,body,args));
                let instance=ty::Instance{def:ty::InstanceKind::Item(owner),args};
                let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
                let expected=generic_mir::capture(tcx,&actual,|span|{let next=spans.len()as u64;*spans.entry(span).or_insert(next)}).unwrap();
                let arguments=args.iter().map(|arg|generic_material::argument(tcx,arg).unwrap()).collect::<Vec<_>>().join(",");
                let mut locations=vec![String::new();spans.len()];
                for (span,index) in &spans {
                    locations[*index as usize]=format!("{{\"lo\":{},\"hi\":{},\"ctxt\":{:?}}}",span.lo().0,span.hi().0,format!("{:?}",span.ctxt()));
                }
                rows.push(format!("{{\"source\":{source},\"arguments\":[{arguments}],\"expected\":{expected},\"spans\":[{}]}}",locations.join(",")));
            }
        }
        assert_eq!(rows.len(),4,"oracle fixture must retain exactly one coroutine source");
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
