#![feature(rustc_private)]
//! Test-only pinned compiler sizedness oracle for novel ADT instantiations.
extern crate rustc_driver;
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::ty::{self,Ty,TyCtxt};
use rustc_hir::def::DefKind;
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let find=|name:&str|tcx.hir_crate_items(()).definitions()
            .find(|def|tcx.def_kind(*def)==DefKind::Struct && tcx.item_name(def.to_def_id()).as_str()==name)
            .expect("fixture struct absent").to_def_id();
        let tail=tcx.adt_def(find("Tail"));let pointer=tcx.adt_def(find("PointerTail"));
        let slice=Ty::new_slice(tcx,tcx.types.u16);
        let tail_str=Ty::new_adt(tcx,tail,tcx.mk_args(&[tcx.types.str_.into()]));
        let mut rows=Vec::new();
        let types=[tcx.types.u8,tcx.types.str_,slice,
            Ty::new_adt(tcx,tail,tcx.mk_args(&[tcx.types.u8.into()])),tail_str,
            Ty::new_adt(tcx,tail,tcx.mk_args(&[slice.into()])),
            Ty::new_adt(tcx,tail,tcx.mk_args(&[tail_str.into()])),
            Ty::new_adt(tcx,pointer,tcx.mk_args(&[tcx.types.str_.into()])),
            Ty::new_tup(tcx,&[tcx.types.u8,tcx.types.str_])];
        for ty in types {
            let sized=ty.is_sized(tcx,ty::TypingEnv::fully_monomorphized());
            let meta=tcx.lang_items().get(rustc_attr_ir::LangItem::MetaSized).expect("MetaSized lang item");
            let goal=ty::TraitRef::new(tcx,meta,[ty]);
            let meta_sized=match tcx.codegen_select_candidate(ty::TypingEnv::fully_monomorphized().as_query_input(goal)) {
                Ok(_)=>true,
                Err(rustc_middle::traits::CodegenObligationError::Unimplemented)=>false,
                Err(error)=>panic!("unexpected MetaSized oracle ambiguity: {error:?}"),
            };
            rows.push(format!("{{\"type\":{},\"is_sized\":{sized},\"is_meta_sized\":{meta_sized}}}",generic_material::type_tree(tcx,ty).expect("oracle type tree")));
        }
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
