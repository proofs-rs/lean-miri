//! Actual pinned optimized-MIR source/category inventory, normalized full-body
//! oracles and source-admission mutations. It never supplies runtime answers.
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
use rustc_middle::{mir,ty};
use rustc_middle::ty::TypeVisitableExt;
use rustc_driver::{Callbacks,Compilation};
fn q(value:&str)->String {format!("{:?}",value)}
struct Inspector;
impl Callbacks for Inspector {
 fn after_analysis<'tcx>(&mut self,_:&rustc_interface::interface::Compiler,tcx:ty::TyCtxt<'tcx>)->Compilation {
  tcx.dcx().abort_if_errors();
  let output=std::path::PathBuf::from(std::env::var_os("EXTENDED_SOURCE_MIR_OUT").unwrap_or_else(||"scratch/extended-source-mir".into()));
  std::fs::create_dir_all(&output).unwrap();
  let mut entries=Vec::new();let mut owners=Vec::new();
  for definition in tcx.hir_crate_items(()).definitions() {
   if tcx.def_kind(definition)!=rustc_hir::def::DefKind::Fn {continue}
   let body=tcx.optimized_mir(definition);
   let name=tcx.item_name(definition.to_def_id()).to_string();
   if name.starts_with("ordinary_") {entries.push((name.clone(),definition.to_def_id(),ty::GenericArgs::identity_for_item(tcx,definition)));}
   for block in body.basic_blocks.iter() {for statement in &block.statements {
    let mir::StatementKind::Assign(pair)=&statement.kind else {continue};
    let mir::Rvalue::Aggregate(kind,_)=&pair.1 else {continue};
    let mir::AggregateKind::Coroutine(owner,args)=&**kind else {continue};
    if !owners.contains(owner) {owners.push(*owner);entries.push((name.clone(),*owner,*args));}
   }}
  }
  let mut rows=Vec::new();let mut oracles=Vec::new();let mut controls=Vec::new();let mut interface_controls=Vec::new();
  for (name,owner,args) in entries {
   let body=tcx.optimized_mir(owner);
   let mut pretty_mir=Vec::new();mir::pretty::MirWriter::new(tcx).write_mir_fn(body,&mut pretty_mir).unwrap();
   std::fs::write(output.join(format!("{name}.mir")),pretty_mir).unwrap();
   if name=="ordinary_fn_item_local" {
    for replacement in [tcx.types.u8,tcx.types.u64,tcx.types.bool,tcx.types.i128] {
     let closed=tcx.mk_args(&[replacement.into()]);
     let interface=generic_mir::interface(tcx,body,closed).unwrap();
     let instance=ty::Instance{def:ty::InstanceKind::Item(owner),args:closed};
     let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
     assert_eq!(interface.return_type,actual.local_decls[mir::RETURN_PLACE].ty);
     assert_eq!(interface.argument_count,actual.arg_count);
     for (local,ty) in interface.arguments {assert_eq!(ty,actual.local_decls[local].ty);}
     interface_controls.push(format!("{{\"name\":{},\"argument\":{}}}",q(&name),q(&format!("{replacement:?}"))));
    }
   }
   let mut spans=std::collections::HashMap::new();
   let category=generic_mir::source_category(tcx,body,args);
   let captured=match category {
    Some(category)=>generic_mir::capture_category(tcx,body,category,|span|{let next=spans.len() as u64;*spans.entry(span).or_insert(next)}),
    None=>Err(generic_mir::capture_extended(tcx,body,|_|0).err().unwrap_or_else(||"source arguments are outside the selected category".into())),
   };
   let source=match captured {Ok(value)=>{
    std::fs::write(output.join(format!("{name}.source.json")),&value).unwrap();
    let mut reject=|label:&str,changed:&mir::Body<'tcx>,expected:&str| {
     let error=generic_mir::capture_extended(tcx,changed,|_|0).unwrap_err();
     assert_eq!(error,expected,"raw source admission control {name}/{label}");
     controls.push(format!("{{\"name\":{},\"control\":{},\"error\":{}}}",q(&name),q(label),q(&error)));
    };
    let mut wrong_phase=body.clone();wrong_phase.phase=mir::MirPhase::Runtime(mir::RuntimePhase::Initial);
    reject("wrong-phase",&wrong_phase,"copy template requires optimized runtime MIR");
    let mut absent_required=body.clone();absent_required.required_consts=None;
    reject("missing-required-constants",&absent_required,"copy template requires an empty explicit required-constants list");
    let mut nonerased=body.clone();let mut changed=false;
    for block in nonerased.basic_blocks_mut().iter_mut() {for statement in &mut block.statements {
     if let mir::StatementKind::Assign(pair)=&mut statement.kind {
      if let mir::Rvalue::Ref(region,_,_)=&mut pair.1 {*region=tcx.lifetimes.re_static;changed=true;}
     }
    }}
    if changed {reject("nonerased-reference",&nonerased,"source Ref requires explicit raw erased region");}
    let mut nonnormal=body.clone();let mut changed=false;
    for block in nonnormal.basic_blocks_mut().iter_mut() {
     if let mir::TerminatorKind::Call{call_source,..}=&mut block.terminator_mut().kind {*call_source=mir::CallSource::OverloadedOperator;changed=true;}
    }
    if changed {reject("nonnormal-call",&nonnormal,"source call kind outside normal source");}
    let mut unsupported_cast=body.clone();let mut changed=false;
    for block in unsupported_cast.basic_blocks_mut().iter_mut() {for statement in &mut block.statements {
     if let mir::StatementKind::Assign(pair)=&mut statement.kind {
      if let mir::Rvalue::Cast(kind,_,_)=&mut pair.1 {
       *kind=mir::CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize,mir::CoercionSource::Implicit);changed=true;
      }
     }
    }}
    if changed {reject("unsupported-pointer-coercion",&unsupported_cast,"source cast kind outside supported source grammar");}
    let generics=tcx.generics_of(owner);let parents=if body.coroutine.is_some(){generics.parent_count}else{generics.count()};
    let type_generic=(0..parents).any(|index|matches!(generics.param_at(index,tcx).kind,ty::GenericParamDefKind::Type{..}));
    for replacement in [tcx.types.u8,tcx.types.u64,tcx.types.bool,tcx.types.i128].into_iter().take(if type_generic{4}else{1}) {
     let parent_args=tcx.mk_args_from_iter((0..parents).map(|index|->ty::GenericArg<'tcx>{match generics.param_at(index,tcx).kind {
      ty::GenericParamDefKind::Lifetime=>tcx.lifetimes.re_erased.into(),
      ty::GenericParamDefKind::Type{..}=>replacement.into(),
      ty::GenericParamDefKind::Const{..}=>ty::Const::from_target_usize(tcx,3).into(),
     }}));
     let closed=ty::EarlyBinder::bind(tcx,args).instantiate(tcx,parent_args).skip_normalization();
     let instance=ty::Instance{def:ty::InstanceKind::Item(owner),args:closed};
     let actual=instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,body.typing_env(tcx),ty::EarlyBinder::bind(tcx,body.clone())).unwrap();
     assert!(!actual.has_non_region_param() && !actual.has_escaping_bound_vars() && !actual.has_infer() && !actual.has_placeholders() && !actual.references_error(),"normalized actual body retains unresolved compiler syntax");
     assert_eq!(actual.source.instance.def_id(),owner);
     assert_eq!(actual.source.promoted,body.source.promoted);
     assert_eq!(actual.phase,body.phase);
     let interface=generic_mir::interface(tcx,body,closed).unwrap();
     assert_eq!(interface.argument_count,actual.arg_count);
     assert_eq!(interface.spread_argument,actual.spread_arg);
     assert_eq!(interface.return_type,actual.local_decls[mir::RETURN_PLACE].ty);
     for (local,ty) in interface.arguments {assert_eq!(ty,actual.local_decls[local].ty);}

     let expected=generic_mir::capture_category(tcx,&actual,category.unwrap(),|span|{let next=spans.len() as u64;*spans.entry(span).or_insert(next)}).unwrap();
     let mut locations=vec![String::new();spans.len()];
     for (span,index) in &spans {locations[*index as usize]=format!("{{\"lo\":{},\"hi\":{},\"ctxt\":{}}}",span.lo().0,span.hi().0,q(&format!("{:?}",span.ctxt())));}
     let locations=locations.join(",");
     let arguments=closed.iter().map(|argument|generic_material::argument(tcx,argument).unwrap()).collect::<Vec<_>>().join(",");
     oracles.push(format!("{{\"name\":{},\"physical_owner\":{{\"crate\":{},\"index\":{}}},\"source_role\":\"runtime\",\"source\":{value},\"arguments\":[{arguments}],\"expected\":{expected},\"spans\":[{locations}]}}",q(&name),owner.krate.as_u32(),owner.index.as_u32()));
    }
    "null".to_string()
   },Err(error)=>q(&error)};
   let statements=body.basic_blocks.iter().flat_map(|block|block.statements.iter().map(|statement|q(&format!("{:?}",statement.kind)))).collect::<Vec<_>>().join(",");
   let terminators=body.basic_blocks.iter().map(|block|q(&format!("{:?}",block.terminator().kind))).collect::<Vec<_>>().join(",");
   rows.push(format!("{{\"name\":{},\"owner\":{},\"coroutine\":{},\"eligible\":{},\"first_error\":{source},\"statements\":[{statements}],\"terminators\":[{terminators}]}}",q(&name),owner.index.as_u32(),body.coroutine.is_some(),category.is_some()));
  }
  std::fs::write(output.join("interface-controls.json"),format!("[{}]",interface_controls.join(","))).unwrap();
  std::fs::write(output.join("negative-controls.json"),format!("[{}]",controls.join(","))).unwrap();
  std::fs::write(output.join("oracle.json"),format!("[{}]",oracles.join(","))).unwrap();
  println!("[{}]",rows.join(","));Compilation::Stop
 }
}
fn main()->std::process::ExitCode {
 let args=std::env::args().collect::<Vec<_>>();
 rustc_driver::catch_with_exit_code(||rustc_driver::compiler_entrypoint(&args,&mut Inspector))
}
