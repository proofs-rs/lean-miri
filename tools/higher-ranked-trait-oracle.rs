#![feature(rustc_private)]
//! Independent obligation fulfillment, including genuine forall/static failures.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_infer;
extern crate rustc_trait_selection;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::{ty::{self,TyCtxt},traits::ObligationCause};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_trait_selection::traits::{Obligation,ObligationCtxt};
fn identity(def:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>)->String {
    args.iter().map(|arg|generic_material::argument(tcx,arg).expect("raw argument"))
        .collect::<Vec<_>>().join(",")
}
fn reference<'tcx>(tcx:TyCtxt<'tcx>,value:ty::TraitRef<'tcx>)->String {
    format!("{{\"definition\":{},\"arguments\":[{}]}}",identity(value.def_id),arguments(tcx,value.args))
}
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let find=|kind,name:&str|tcx.hir_crate_items(()).definitions()
            .find(|def|tcx.def_kind(*def)==kind&&tcx.item_name(def.to_def_id()).as_str()==name)
            .expect("higher-ranked fixture declaration").to_def_id();
        let self_ty=tcx.type_of(find(DefKind::Struct,"S")).instantiate_identity().skip_norm_wip();
        let env=ty::TypingEnv::fully_monomorphized();
        let mut rows=Vec::new();
        for (function,trait_name) in [("all","All"),("static_only","StaticOnly"),
            ("type_any","TypeAny"),("repeated","Repeated"),("distinct","Distinct"),
            ("fn_for","FnFor"),("fn_static","FnStatic"),("fn_general_vs_static","FnGeneralVsStatic")] {
            let trait_def=find(DefKind::Trait,trait_name);
            let predicates=tcx.explicit_clauses_of(find(DefKind::Fn,function)).instantiate(tcx,tcx.mk_args(&[self_ty.into()]));
            let clause=*predicates.clauses.iter().find(|predicate|
                predicate.skip_norm_wip().as_trait_clause().is_some_and(|value|value.skip_binder().trait_ref.def_id==trait_def))
                .expect("source quantified trait predicate");
            let clause=clause.skip_norm_wip();
            let goal=clause.as_trait_clause().unwrap();
            let (infcx,param_env)=tcx.infer_ctxt().build_with_typing_env(env);
            let ocx=ObligationCtxt::new(&infcx);
            ocx.register_obligation(Obligation::new(tcx,ObligationCause::dummy(),param_env,clause.as_predicate()));
            let accepted=ocx.evaluate_obligations_error_on_ambiguity().no_errors();
            let implementations=tcx.all_impls(trait_def).collect::<Vec<_>>();
            assert_eq!(implementations.len(),1,"one raw impl per oracle trait");
            let implementation=implementations[0];
            let head=tcx.impl_trait_ref(implementation).instantiate_identity().skip_norm_wip();
            let generics=tcx.generics_of(implementation);
            let parameters=(0..generics.count()).map(|index|match generics.param_at(index,tcx).kind {
                ty::GenericParamDefKind::Lifetime=>"\"region\"",ty::GenericParamDefKind::Type{..}=>"\"type\"",
                ty::GenericParamDefKind::Const{..}=>"\"constant\"",
            }).collect::<Vec<_>>().join(",");
            let variables=goal.bound_vars().iter().map(generic_material::bound_variable).collect::<Vec<_>>().join(",");
            rows.push(format!("{{\"name\":\"{function}\",\"accepted\":{accepted},\"implementation\":{{\"definition\":{},\"parameters\":[{parameters}],\"trait_ref\":{}}},\"goal\":{{\"variables\":[{variables}],\"predicate\":{{\"kind\":\"trait\",\"polarity\":\"positive\",\"trait_ref\":{}}}}}}}",
                identity(implementation),reference(tcx,head),reference(tcx,goal.skip_binder().trait_ref)));
        }
        println!("[{}]",rows.join(","));
        Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args=std::env::args().collect::<Vec<_>>();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
