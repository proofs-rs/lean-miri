#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
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
        let adt=|name,args:&[ty::GenericArg<'tcx>]|Ty::new_adt(tcx,tcx.adt_def(find(DefKind::Struct,name)),tcx.mk_args(args));
        let plain=adt("Plain",&[tcx.types.u16.into()]);
        let denied=adt("Denied",&[]);
        let recursive=adt("Recursive",&[]);
        let types=[(adt("Plain",&[tcx.types.u8.into()]),false,false),(plain,true,false),
            (Ty::new_array(tcx,plain,2),true,false),(adt("Manual",&[]),false,false),
            (denied,false,false),(adt("UnsafeField",&[]),false,false),
            (Ty::new_imm_ptr(tcx,denied),false,false),(Ty::new_array(tcx,denied,0),false,false),
            (recursive,false,true),(Ty::new_array(tcx,recursive,2),true,true),
            (adt("RecursiveDenied",&[]),false,true),
            (Ty::new_array(tcx,adt("RecursiveDenied",&[]),2),true,true)];
        let definition=find(DefKind::Trait,"Mark");
        let mut rows=Vec::new();let mut negative=0;
        for (self_ty,novel,coinductive_boundary) in types {
            let goal=tcx.erase_and_anonymize_regions(ty::TraitRef::new(tcx,definition,[self_ty]));
            let expected=match tcx.codegen_select_candidate(ty::TypingEnv::fully_monomorphized().as_query_input(goal)) {
                Ok(ImplSource::UserDefined(data))=>format!("{{\"kind\":\"implementation\",\"definition\":{},\"arguments\":[{}]}}",identity(data.impl_def_id),arguments(tcx,data.args)),
                Ok(ImplSource::Builtin(_, _))=>"{\"kind\":\"builtin\"}".to_owned(),
                Err(CodegenObligationError::Unimplemented)=>{negative+=1;"{\"kind\":\"no_solution\"}".to_owned()},
                _=>panic!("unexpected ambiguous/parameter candidate"),
            };
            rows.push(format!("{{\"novel_goal\":{novel},\"coinductive_boundary\":{coinductive_boundary},\"goal\":{{\"definition\":{},\"arguments\":[{}]}},\"expected\":{expected}}}",identity(definition),arguments(tcx,goal.args)));
        }
        assert_eq!(negative,6);
        println!("[{}]",rows.join(","));Compilation::Stop
    }
}
fn main()->std::process::ExitCode {let args:Vec<_>=std::env::args().collect();rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))}
