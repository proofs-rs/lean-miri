//! Raw external u64 constant source. No const evaluation, normalization,
//! instance selection, layout, ABI or allocation query is performed here.
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::{mir,ty::{self,TyCtxt}};
use rustc_span::Span;
use serde_json::{json,Value};
/// Pinned rmeta/encoder.rs::encode_mir stores trivial_const instead of
/// mir_for_ctfe when the constant has a trivial representation. Optimized-MIR
/// availability is a separate bit and cannot guard external constant CTFE MIR.
/// Required trait members and directly represented type constants have no RHS.
pub(super) fn const_body_available(tcx:TyCtxt<'_>,definition:DefId)->Option<bool> {
 let has_rhs=match tcx.def_kind(definition) {
  DefKind::AnonConst=>true,
  DefKind::Const=>tcx.const_of_item(definition).is_none(),
  DefKind::AssocConst=>tcx.associated_item(definition).defaultness(tcx).has_value() && tcx.const_of_item(definition).is_none(),
  _=>return None,
 };
 // Short-circuit before querying a required associated constant. For external
 // items a trivial representation means no CTFE MIR was encoded. This source
 // policy consumes MIR only; a trivial value is not an executable body.
 Some(has_rhs && tcx.trivial_const(definition).is_none())
}
fn identity(def:DefId)->Value {json!({"crate":def.krate.as_u32(),"index":def.index.as_u32()})}
fn u64_type(value:ty::Ty<'_>)->Result<(),String> {
 if matches!(value.kind(),ty::Uint(ty::UintTy::U64)){Ok(())}else{Err(format!("type-const source requires raw u64, got {value:?}"))}
}
fn reference<'tcx>(tcx:TyCtxt<'tcx>,value:&mir::ConstOperand<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {
 if value.user_ty.is_some(){return Err("type-const source user-type annotation material is unavailable".into())}
 u64_type(value.const_.ty())?;
 let mir::Const::Unevaluated(source,_)=value.const_ else{return Err("type-const reference requires raw MIR Unevaluated".into())};
 if source.promoted.is_some(){return Err("type-const source promoted operand is outside this policy".into())}
 let args=source.args.iter().map(|value|serde_json::from_str::<Value>(&super::generic_material::argument(tcx,value)?).map_err(|e|e.to_string())).collect::<Result<Vec<_>,String>>()?;
 Ok(json!({"kind":"unevaluated","definition":identity(source.def),"arguments":args,"declared_type":{"kind":"uint","bits":64},"promoted":Value::Null,"span":span(value.span),"user_type":Value::Null}))
}
fn place<'tcx>(body:&mir::Body<'tcx>,value:mir::Place<'tcx>)->Result<Value,String> {
 if !value.projection.is_empty(){return Err("type-const scalar source projection unsupported".into())}
 u64_type(body.local_decls[value.local].ty)?;Ok(json!({"local":value.local.as_u32(),"fields":[]}))
}
fn operand<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,value:&mir::Operand<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {Ok(match value{
 mir::Operand::Copy(value)=>json!({"kind":"copy","place":place(body,*value)?}),
 mir::Operand::Move(value)=>json!({"kind":"move","place":place(body,*value)?}),
 mir::Operand::Constant(value)=>{
  if matches!(value.const_,mir::Const::Unevaluated(..)){json!({"kind":"constant","source":reference(tcx,value,span)?})}else{
   if value.user_ty.is_some(){return Err("type-const source has unavailable annotation".into())}
   u64_type(value.const_.ty())?;
   let class=match value.const_ {mir::Const::Val(..)=>"literal_value",mir::Const::Ty(declared,constant)=>match constant.kind(){ty::ConstKind::Value(v) if declared==v.ty=>"type_value",_=>return Err("type-const source Ty operand is not raw Value".into())},_=>return Err("type-const source operand is not a raw value".into())};
   let scalar=value.const_.try_to_scalar_int().ok_or("type-const source raw value is not ScalarInt")?;
   if scalar.size().bytes()!=8{return Err("type-const source raw u64 width mismatch".into())}
   json!({"kind":"source_value","source_class":class,"span":span(value.span),"user_type":Value::Null,"value":{"kind":"uint","bits":64,"value":scalar.to_bits_unchecked().to_string()}})
  }
 },_=>return Err("type-const source runtime-check operand unsupported".into()),
})}
pub(super) fn capture<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId,body:&mir::Body<'tcx>,mut span:impl FnMut(Span)->u64)->Result<Value,String>{
 let owner_kind=match tcx.def_kind(definition){DefKind::AnonConst=>"anon_const",DefKind::AssocConst=>"associated_const",DefKind::Const=>"const",_=>return Err("type-const source definition kind unsupported".into())};
 if body.source.def_id()!=definition || body.source.promoted.is_some(){return Err("type-const raw body owner/promoted mismatch".into())}
 if body.phase!=mir::MirPhase::Runtime(mir::RuntimePhase::PostCleanup) || body.arg_count!=0 || body.spread_arg.is_some() || body.coroutine.is_some() || body.injection_phase.is_some() || !body.user_type_annotations.is_empty(){return Err("type-const raw frame policy mismatch".into())}
 if tcx.generics_of(definition).count()!=0{return Err("type-const source needs separate generic-frame admission".into())}
 if body.basic_blocks.len()!=1{return Err("type-const source requires a single raw return block".into())}
 let block=&body.basic_blocks[mir::START_BLOCK];
 if block.is_cleanup || !matches!(block.terminator().kind,mir::TerminatorKind::Return){return Err("type-const source requires normal Return".into())}
 let info=|v:mir::SourceInfo,span:&mut dyn FnMut(Span)->u64|json!({"span":span(v.span),"scope":v.scope.as_u32()});
 let locals=body.local_decls.iter().map(|v|{u64_type(v.ty)?;Ok(json!({"type":{"kind":"uint","bits":64},"source":info(v.source_info,&mut span),"mutable":v.mutability.is_mut()}))}).collect::<Result<Vec<_>,String>>()?;
 let statements=block.statements.iter().map(|s|{let kind=match &s.kind{
  mir::StatementKind::StorageLive(n)=>json!({"kind":"storage_live","local":n.as_u32()}),mir::StatementKind::StorageDead(n)=>json!({"kind":"storage_dead","local":n.as_u32()}),mir::StatementKind::Nop=>json!({"kind":"nop"}),mir::StatementKind::ConstEvalCounter=>json!({"kind":"const_eval_counter"}),
  mir::StatementKind::Assign(pair)=>{let value=match &pair.1{
   mir::Rvalue::Use(v,retag)=>json!({"kind":"use","operand":operand(tcx,body,v,&mut span)?,"retag":match retag{mir::WithRetag::Yes=>"yes",mir::WithRetag::No=>"no"}}),
   mir::Rvalue::UnaryOp(mir::UnOp::Not,v)=>json!({"kind":"unary","op":"not","operand":operand(tcx,body,v,&mut span)?}),
   other=>return Err(format!("type-const source rvalue unsupported {other:?}")),
  };json!({"kind":"assign","destination":place(body,pair.0)?,"value":value})},
  other=>return Err(format!("type-const source statement unsupported {other:?}")),
 };Ok(json!({"source":info(s.source_info,&mut span),"kind":kind}))}).collect::<Result<Vec<_>,String>>()?;
 let required=body.required_consts.as_ref().ok_or("type-const source lacks required-constant domain")?.iter().map(|v|reference(tcx,v,&mut span)).collect::<Result<Vec<_>,_>>()?;
 let scopes=body.source_scopes.iter().map(|s|{let lint=match &s.local_data{mir::ClearCrossCrate::Set(d)=>json!({"owner":identity(d.lint_root.owner.def_id.to_def_id()),"local_id":d.lint_root.local_id.as_u32()}),mir::ClearCrossCrate::Clear=>Value::Null};json!({"span":span(s.span),"parent":s.parent_scope.map(|n|n.as_u32()),"lint_root":lint})}).collect::<Vec<_>>();
 Ok(json!({"definition":identity(definition),"owner_kind":owner_kind,"source_role":"ctfe","def_path":tcx.def_path_str(definition),"preamble_def_span":span(tcx.def_span(definition)),"promoted":Value::Null,"policy":"u64_physical_constants_v1","phase":"runtime_post_cleanup","environment_recipe":{"kind":"declaration","owner":identity(definition),"mode":"post_analysis"},"parameters":[],"user_type_annotations":[],"required_consts":required,"span":span(body.span),"arg_count":0,"spread_arg":Value::Null,"locals":locals,"blocks":[{"cleanup":false,"statements":statements,"terminator":{"source":info(block.terminator().source_info,&mut span),"kind":{"kind":"return"}}}],"source_scopes":scopes}))
}
