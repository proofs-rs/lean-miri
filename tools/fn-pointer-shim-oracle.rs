#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_attr_ir;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;
#[path="../exporter/src/generic_material.rs"] mod generic_material;
use rustc_driver::{Callbacks,Compilation};
use rustc_middle::{mir,ty::{self,TyCtxt}};
struct Oracle;
fn body_json<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, span:rustc_span::Span)->String {
    assert_eq!(body.phase,mir::MirPhase::Runtime(mir::RuntimePhase::Optimized));
    assert_eq!(body.span,span);
    assert_eq!(body.source_scopes.len(),1);
    let scope=&body.source_scopes[mir::OUTERMOST_SOURCE_SCOPE];
    assert_eq!(scope.span,span);
    assert!(scope.parent_scope.is_none() && scope.inlined.is_none() && scope.inlined_parent_scope.is_none());
    assert!(body.required_consts.as_ref().unwrap().is_empty());
    assert!(body.injection_phase.is_none() && body.coroutine.is_none());
    let check_info=|info:mir::SourceInfo| {assert_eq!(info.span,span);assert_eq!(info.scope,mir::OUTERMOST_SOURCE_SCOPE);};
    let locals=body.local_decls.iter().map(|local| {
        check_info(local.source_info);
        generic_material::type_tree(tcx,local.ty).unwrap()
    }).collect::<Vec<_>>();
    let mut blocks=Vec::new();
    for block in body.basic_blocks.iter() {
        let mut statements=Vec::new();
        for statement in &block.statements {
            check_info(statement.source_info);
            let mir::StatementKind::Assign(pair)=&statement.kind else {panic!("unexpected statement: {:?}",statement.kind)};
            assert!(pair.0.projection.is_empty());
            let mir::Rvalue::Cast(kind,operand,target)=&pair.1 else {panic!("unexpected rvalue: {:?}",pair.1)};
            let cast=match kind {mir::CastKind::Transmute=>"transmute",mir::CastKind::FnPtrToPtr=>"fn_ptr_to_ptr",other=>panic!("unexpected cast: {other:?}")};
            let mir::Operand::Move(place)=operand else {panic!("unexpected operand: {operand:?}")};
            assert!(place.projection.is_empty());
            statements.push(format!("{{\"destination\":{},\"cast\":\"{cast}\",\"operand\":{},\"target\":{}}}",
                pair.0.local.as_u32(),place.local.as_u32(),generic_material::type_tree(tcx,*target).unwrap()));
        }
        check_info(block.terminator().source_info);
        assert!(matches!(block.terminator().kind,mir::TerminatorKind::Return));
        blocks.push(format!("{{\"statements\":[{}],\"terminator\":\"return\",\"cleanup\":{}}}",statements.join(","),block.is_cleanup));
    }
    format!("{{\"phase\":\"runtime_optimized\",\"argument_count\":{},\"spread_argument\":{},\"locals\":[{}],\"blocks\":[{}]}}",
        body.arg_count,body.spread_arg.map_or("null".to_owned(),|local|local.as_u32().to_string()),locals.join(","),blocks.join(","))
}
impl Callbacks for Oracle {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:TyCtxt<'tcx>)->Compilation {
    tcx.dcx().abort_if_errors();
    let mut pointers=Vec::new();
    for local in tcx.hir_crate_items(()).definitions() {
        let id=local.to_def_id();
        if matches!(tcx.def_kind(id),rustc_hir::def::DefKind::TyAlias) {
            let ty=tcx.type_of(id).instantiate_identity().skip_norm_wip();
            if matches!(ty.kind(),ty::FnPtr(..)) {pointers.push(ty);}
        }
    }
    assert!(pointers.len()>=4);
    let as_def=tcx.lang_items().fn_ptr_as_ptr().unwrap();
    let from_def=tcx.lang_items().fn_ptr_from_ptr().unwrap();
    let nonnull=tcx.require_lang_item(rustc_attr_ir::lang_items::LangItem::NonNull,rustc_span::DUMMY_SP);
    let code=tcx.lang_items().code().unwrap();
    let nonnull=tcx.type_of(nonnull).instantiate(tcx,&[tcx.type_of(code).instantiate_identity().skip_norm_wip().into()]).skip_norm_wip();
    let mut rows=Vec::new();
    for pointer in pointers {
        for (tag,def,shim) in [("as_pointer",as_def,ty::ShimKind::FnPtrAsPtr(as_def,pointer)),
            ("from_pointer",from_def,ty::ShimKind::FnPtrFromPtr(from_def,pointer))] {
            let signature=generic_material::signature_tree(tcx,tcx.fn_sig(def).instantiate_identity().skip_norm_wip()).unwrap();
            let body=tcx.instance_mir(ty::InstanceKind::Shim(shim));
            rows.push(format!("{{\"kind\":\"{tag}\",\"signature\":{signature},\"self_type\":{},\"non_null_type\":{},\"expected\":{}}}",
                generic_material::type_tree(tcx,pointer).unwrap(),generic_material::type_tree(tcx,nonnull).unwrap(),body_json(tcx,body,tcx.def_span(def))));
        }
    }
    println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {
 let args:Vec<_>=std::env::args().collect();
 rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Oracle))
}
