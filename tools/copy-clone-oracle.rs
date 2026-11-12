#![feature(rustc_private)]
//! Test-only independent candidate-selection oracle, never producer material.
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
extern crate rustc_attr_ir;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{ty::{self,TyCtxt,Ty},traits::{ImplSource,CodegenObligationError}};
use rustc_hir::{def::DefKind,def_id::DefId};
fn identity(def:DefId)->String {format!("{{\"crate\":{},\"index\":{}}}",def.krate.as_u32(),def.index.as_u32())}
fn arguments<'tcx>(tcx:TyCtxt<'tcx>,args:ty::GenericArgsRef<'tcx>)->String {
    args.iter().map(|arg|generic_material::argument(tcx,arg).expect("typed oracle argument")).collect::<Vec<_>>().join(",")
}
struct Oracle;
impl Callbacks for Oracle {
    fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
        tcx.dcx().abort_if_errors();
        let find=|kind,name:&str|tcx.hir_crate_items(()).definitions()
            .find(|def|tcx.def_kind(*def)==kind&&tcx.item_name(def.to_def_id()).as_str()==name)
            .expect("fixture declaration absent").to_def_id();
        let shared=Ty::new_imm_ref(tcx,tcx.lifetimes.re_static,tcx.types.u8);
        let unique=Ty::new_mut_ref(tcx,tcx.lifetimes.re_static,tcx.types.u8);
        let conditional=tcx.adt_def(find(DefKind::Struct,"Conditional"));
        let cond=|t:Ty<'tcx>|Ty::new_adt(tcx,conditional,tcx.mk_args(&[t.into()]));
        let fndef=Ty::new_fn_def(tcx,find(DefKind::Fn,"source_function"),ty::Binder::dummy([tcx.types.u16]));
        let fnptr=Ty::new_fn_ptr(tcx,tcx.fn_sig(find(DefKind::Fn,"pointer_signature")).instantiate_identity().skip_norm_wip());
        let types=[tcx.types.u8,shared,unique,Ty::new_imm_ptr(tcx,tcx.types.str_),
            Ty::new_tup(tcx,&[tcx.types.u8,tcx.types.u16]),Ty::new_tup(tcx,&[tcx.types.u8,unique]),
            cond(tcx.types.u16),cond(unique),Ty::new_adt(tcx,tcx.adt_def(find(DefKind::Struct,"Plain")),tcx.mk_args(&[])),
            fndef,fnptr,Ty::new_array(tcx,cond(tcx.types.u16),2),Ty::new_array(tcx,unique,0)];
        let mut rows=Vec::new();let mut negative=0;let mut positive=0;
        for lang in [rustc_attr_ir::LangItem::Copy,rustc_attr_ir::LangItem::Clone] {
            let definition=tcx.lang_items().get(lang).expect("required trait lang item");
            for (index,self_ty) in types.iter().enumerate() {
                let goal=tcx.erase_and_anonymize_regions(ty::TraitRef::new(tcx,definition,[*self_ty]));
                let expected=match tcx.codegen_select_candidate(ty::TypingEnv::fully_monomorphized().as_query_input(goal)) {
                    Ok(ImplSource::UserDefined(data))=>{positive+=1;format!("{{\"kind\":\"implementation\",\"definition\":{},\"arguments\":[{}]}}",identity(data.impl_def_id),arguments(tcx,data.args))},
                    Ok(ImplSource::Builtin(_, _))=>{positive+=1;"{\"kind\":\"builtin\"}".to_owned()},
                    Err(CodegenObligationError::Unimplemented)=>{negative+=1;"{\"kind\":\"no_solution\"}".to_owned()},
                    _=>panic!("unexpected ambiguous/parameter candidate"),
                };
                rows.push(format!("{{\"novel_goal\":{},\"goal\":{{\"definition\":{},\"arguments\":[{}]}},\"expected\":{expected}}}",index==6||index==9||index==10||index>=11,identity(definition),arguments(tcx,goal.args)));
            }
        }
        assert!(positive>=10&&negative>=6);
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {
    let args:Vec<_>=std::env::args().collect();
    rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
