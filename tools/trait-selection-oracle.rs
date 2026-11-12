#![feature(rustc_private)]
//! Test-only independent rustc selection oracle. Fixture names locate source
//! declarations; the compared goals, impl identities and substitutions are typed
//! physical data. This is never linked into the production material exporter.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{ty::{self,TyCtxt},traits::{ImplSource,CodegenObligationError}};
use rustc_hir::{def::DefKind,def_id::DefId};
fn identity(def:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>)->String {
    args.iter().map(|arg|generic_material::argument(tcx,arg).expect("typed oracle argument")).collect::<Vec<_>>().join(",")
}
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let find=|kind,name:&str| tcx.hir_crate_items(()).definitions()
            .find(|def|tcx.def_kind(*def)==kind&&tcx.item_name(def.to_def_id()).as_str()==name)
            .expect("fixture declaration absent").to_def_id();
        let env=ty::TypingEnv::fully_monomorphized();
        let alias=|name|tcx.try_normalize_erasing_regions(env,tcx.type_of(find(DefKind::TyAlias,name)).instantiate_identity())
            .expect("fixture type alias normalization");
        let good=alias("Good");let bad=alias("Bad");let novel=alias("Novel");
        let mut rows=Vec::new();let mut proven=0;let mut negative=0;
        let outside=tcx.try_normalize_erasing_regions(env,tcx.type_of(find(DefKind::Struct,"Outside")).instantiate_identity()).expect("fixture outside type normalization");
        for (name,self_ty,outside_scope,novel_goal) in [("Gate",good,false,false),("Gate",bad,false,false),("Product",good,false,false),("Product",bad,false,false),("Leaf",tcx.types.u8,false,false),("Leaf",tcx.types.u32,false,false),("Gate",novel,false,true),("Gate",outside,true,false)] {
            let goal=ty::TraitRef::new(tcx,find(DefKind::Trait,name),[self_ty]);
            let expected=match tcx.codegen_select_candidate(env.as_query_input(goal)) {
                Ok(ImplSource::UserDefined(data))=>{proven+=1;format!("{{\"kind\":\"implementation\",\"definition\":{},\"arguments\":[{}]}}",identity(data.impl_def_id),arguments(tcx,data.args))},
                Err(CodegenObligationError::Unimplemented)=>{negative+=1;"{\"kind\":\"no_solution\"}".to_owned()},
                Ok(_)=>panic!("fixture unexpectedly selected a non-source builtin/parameter candidate"),
                Err(_)=>panic!("fixture unexpectedly ambiguous or ill-formed"),
            };
            rows.push(format!("{{\"outside_scope\":{outside_scope},\"novel_goal\":{novel_goal},\"goal\":{{\"definition\":{},\"arguments\":[{}]}},\"expected\":{expected}}}",identity(goal.def_id),arguments(tcx,goal.args)));
        }
        assert_eq!((proven,negative),(5,3));
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
