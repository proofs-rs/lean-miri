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
#[path="../exporter/src/noop_drop.rs"] mod noop_drop;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty::{self,Ty,TyCtxt}};
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let def=tcx.lang_items().drop_glue_fn().unwrap();
        let signature=generic_material::signature_tree(tcx,tcx.fn_sig(def).instantiate_identity().skip_norm_wip()).unwrap();
        let kind=ty::InstanceKind::Shim(ty::ShimKind::DropGlue(def,None));
        let source=tcx.instance_mir(kind);
        assert_eq!(source.basic_blocks.len(),1);
        assert!(matches!(source.basic_blocks[mir::START_BLOCK].terminator().kind,mir::TerminatorKind::Return));
        let mut rows=Vec::new();
        for replacement in [tcx.types.u8,tcx.types.u32,tcx.types.u64,
            Ty::new_tup(tcx,&[tcx.types.u32,tcx.types.u64]),
            Ty::new_imm_ref(tcx,tcx.lifetimes.re_static,tcx.types.u32)] {
            let args=tcx.mk_args(&[replacement.into()]);
            let instance=ty::Instance{def:kind,args};
            assert!(noop_drop::eligible(tcx,instance));
            let interface=noop_drop::interface(tcx,instance).unwrap();
            let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,source.typing_env(tcx),ty::EarlyBinder::bind(tcx,source.clone())).unwrap();
            assert_eq!(interface.argument_count,actual.arg_count);
            assert_eq!(interface.spread_argument,actual.spread_arg);
            assert_eq!(interface.return_type,actual.local_decls[mir::RETURN_PLACE].ty);
            for (local,ty) in interface.arguments {assert_eq!(ty,actual.local_decls[local].ty);}
            let span=tcx.def_span(def);
            let expected=generic_mir::capture(tcx,&actual,|value|{assert_eq!(value,span);0}).unwrap();
            let argument=generic_material::argument(tcx,replacement.into()).unwrap();
            rows.push(format!("{{\"signature\":{signature},\"arguments\":[{argument}],\"expected\":{expected}}}"));
        }
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
