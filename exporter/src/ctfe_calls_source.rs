//! Bounded raw CTFE calls source; a separate wire policy. No evaluation, normalization, layout,
//! selected-instance, compiler allocation, or ABI query is used here.
use rustc_middle::{mir,ty::{self,TyCtxt}};
use rustc_hir::def_id::DefId;
use rustc_span::Span;
use serde_json::{json,Value};

fn identity(def:DefId)->Value {json!({"crate":def.krate.as_u32(),"index":def.index.as_u32()})}
fn shape(ty:ty::Ty<'_>)->Result<Value,String> {Ok(match ty.kind(){
 ty::Uint(ty::UintTy::U32)=>json!({"kind":"uint","bits":32}),
 ty::Bool=>json!({"kind":"boolean"}),ty::Never=>json!({"kind":"never"}),
 ty::Tuple(fields) if fields.is_empty()=>json!({"kind":"unit"}),
 ty::Tuple(fields) if fields.len()==2=>json!({"kind":"pair","left":shape(fields[0])?,"right":shape(fields[1])?}),
 other=>return Err(format!("scalar CTFE source type unsupported: {other:?}")),
})}
fn place<'tcx>(body:&mir::Body<'tcx>,value:mir::Place<'tcx>)->Result<(Value,ty::Ty<'tcx>),String> {
 let mut current=body.local_decls[value.local].ty;let mut fields=Vec::new();
 for field in value.projection.iter(){match field{
  mir::ProjectionElem::Field(index,annotation)=>{
   let ty::Tuple(types)=current.kind() else {return Err("scalar CTFE projection is not a tuple field".into())};
   let child=types.get(index.as_usize()).ok_or("scalar CTFE tuple field absent")?;
   if *child!=annotation {return Err("scalar CTFE field annotation contradicts raw tuple source".into())}
   fields.push(index.as_u32());current=*child;
  },other=>return Err(format!("scalar CTFE projection unsupported: {other:?}")),
 }}
 Ok((json!({"local":value.local.as_u32(),"fields":fields}),current))
}
fn reference(value:&mir::ConstOperand<'_>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {
 if let mir::Const::Ty(declared,constant)=value.const_ {
  if let ty::ConstKind::Param(parameter)=constant.kind() {
   return Ok(json!({"kind":"parameter_constant","index":parameter.index,"declared_type":shape(declared)?,"span":span(value.span),"user_type":value.user_ty.map(|index|index.as_u32())}));
  }
 }
 let mir::Const::Unevaluated(source,declared)=value.const_ else {return Err("required source must retain Unevaluated constructor".into())};
 if !source.def.is_local() || source.promoted.is_some() {return Err("calls policy requires unpromoted local constant".into())}
 let parameter=if source.args.is_empty() {None} else {
  if source.args.len()!=1 {return Err("raw associated source argument arity unsupported".into())}
  let ty::GenericArgKind::Type(arg)=source.args[0].kind() else {return Err("raw source argument is not a type".into())};
  let ty::Param(parameter)=arg.kind() else {return Err("raw source argument is not a parameter".into())};
  Some(parameter.index)
 };
 Ok(json!({"kind":if parameter.is_some(){"associated"}else{"direct"},"definition":identity(source.def),"promoted":null,"arguments":parameter.map(|index|vec![json!({"kind":"type_parameter","index":index})]).unwrap_or_default(),"parameter":parameter,"declared_type":shape(declared)?,"span":span(value.span),"user_type":value.user_ty.map(|index|index.as_u32())}))
}
fn operand<'tcx>(body:&mir::Body<'tcx>,value:&mir::Operand<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {Ok(match value{
 mir::Operand::Copy(value)=>json!({"kind":"copy","place":place(body,*value)?.0}),
 mir::Operand::Move(value)=>json!({"kind":"move","place":place(body,*value)?.0}),
 mir::Operand::Constant(value)=>{
  if matches!(value.const_,mir::Const::Unevaluated(..)) || matches!(value.const_,mir::Const::Ty(_,constant) if matches!(constant.kind(),ty::ConstKind::Param(_))) {
   return Ok(json!({"kind":"constant","source":reference(value,span)?}));
  }
  if value.user_ty.is_some() {return Err("scalar CTFE source requires complete user-type annotation material".into())}
  let class=match value.const_ {
   mir::Const::Ty(declared,constant)=>match constant.kind(){
    ty::ConstKind::Value(source) if declared==source.ty=>"type_value",
    _=>return Err("scalar CTFE source requires a closed canonical Ty(Value)".into()),
   },
   mir::Const::Val(..)=>"literal_value",
   mir::Const::Unevaluated(..)=>return Err("raw Unevaluated requires the separate CTFE query bridge".into()),
  };
  let raw=match value.const_.ty().kind(){
   ty::Uint(ty::UintTy::U32)=>{let scalar=value.const_.try_to_scalar_int().ok_or("non-integer CTFE u32 literal")?;
    if scalar.size().bytes()!=4 {return Err("raw CTFE u32 literal has wrong byte width".into())}
    json!({"kind":"uint","bits":32,"value":scalar.to_bits_unchecked().to_string()})},
   ty::Bool=>{let scalar=value.const_.try_to_scalar_int().ok_or("non-integer CTFE bool literal")?;
    let bits=scalar.to_bits_unchecked();if scalar.size().bytes()!=1 || bits>1 {return Err("invalid raw CTFE bool literal".into())}
    json!({"kind":"boolean","value":bits==1})},
   ty::Tuple(fields) if fields.is_empty()=>{
    match value.const_ {mir::Const::Val(mir::ConstValue::ZeroSized,_)=>{},mir::Const::Ty(_,source)=>{
      let ty::ConstKind::Value(value)=source.kind() else {return Err("raw CTFE unit must retain its source Value".into())};
      if !matches!(**value.valtree,ty::ValTreeKind::Branch(children) if children.is_empty()) {return Err("invalid raw CTFE unit ValTree".into())}
    },_=>return Err("invalid raw CTFE unit source".into())}
    json!({"kind":"unit"})},
   other=>return Err(format!("raw CTFE source literal unsupported: {other:?}")),
  };
  json!({"kind":"source_value","source_class":class,"span":span(value.span),"user_type":null,"value":raw})
 },other=>return Err(format!("scalar CTFE operand unsupported: {other:?}")),
})}
fn operand_shape<'tcx>(body:&mir::Body<'tcx>,value:&mir::Operand<'tcx>)->Result<Value,String> {
 let ty=match value {mir::Operand::Copy(value)|mir::Operand::Move(value)=>place(body,*value)?.1,mir::Operand::Constant(value)=>value.const_.ty(),other=>return Err(format!("scalar CTFE operand type unsupported: {other:?}"))};
 if ty.is_never() {return Err("scalar CTFE uninhabited operand unsupported".into())}
 shape(ty)
}
fn rvalue_shape<'tcx>(body:&mir::Body<'tcx>,value:&mir::Rvalue<'tcx>)->Result<Value,String> {match value {
 mir::Rvalue::Use(value,_)=>operand_shape(body,value),
 mir::Rvalue::BinaryOp(op,args)=>{
  let integer=json!({"kind":"uint","bits":32});
  if operand_shape(body,&args.0)?!=integer || operand_shape(body,&args.1)?!=integer {return Err("scalar CTFE binary operation requires u32 operands".into())}
  match op {mir::BinOp::Gt|mir::BinOp::Eq=>Ok(json!({"kind":"boolean"})),mir::BinOp::Div=>Ok(integer),mir::BinOp::AddWithOverflow|mir::BinOp::SubWithOverflow=>Ok(json!({"kind":"pair","left":integer,"right":{"kind":"boolean"}})),other=>Err(format!("scalar CTFE binary type unsupported: {other:?}"))}
 },other=>Err(format!("scalar CTFE rvalue type unsupported: {other:?}"))}}
fn rvalue<'tcx>(body:&mir::Body<'tcx>,value:&mir::Rvalue<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {Ok(match value{
 mir::Rvalue::Use(value,retag)=>json!({"kind":"use","operand":operand(body,value,span)?,"retag":match retag {mir::WithRetag::Yes=>"yes",mir::WithRetag::No=>"no"}}),
 mir::Rvalue::BinaryOp(op,args)=>{let op=match op {mir::BinOp::Gt=>"gt",mir::BinOp::Eq=>"eq",mir::BinOp::Div=>"div",mir::BinOp::AddWithOverflow=>"add_with_overflow",mir::BinOp::SubWithOverflow=>"sub_with_overflow",other=>return Err(format!("scalar CTFE binary op unsupported: {other:?}"))};json!({"kind":"binary","op":op,"left":operand(body,&args.0,span)?,"right":operand(body,&args.1,span)?})},
 other=>return Err(format!("scalar CTFE rvalue unsupported: {other:?}")),
})}
fn statement<'tcx>(body:&mir::Body<'tcx>,value:&mir::Statement<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {Ok(match &value.kind{
 mir::StatementKind::Assign(value)=>{
  if !value.0.projection.is_empty() {return Err("scalar CTFE projected assignment unsupported".into())}
  let (destination,ty)=place(body,value.0)?;
  if shape(ty)?!=rvalue_shape(body,&value.1)? {return Err("scalar CTFE assignment contradicts raw local type".into())}
  json!({"kind":"assign","destination":destination,"value":rvalue(body,&value.1,span)?})},
 mir::StatementKind::StorageLive(value)=>json!({"kind":"storage_live","local":value.as_u32()}),
 mir::StatementKind::StorageDead(value)=>json!({"kind":"storage_dead","local":value.as_u32()}),
 mir::StatementKind::ConstEvalCounter=>json!({"kind":"const_eval_counter"}),mir::StatementKind::Nop=>json!({"kind":"nop"}),
 other=>return Err(format!("scalar CTFE statement unsupported: {other:?}")),
})}
fn terminator<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,value:&mir::Terminator<'tcx>,span:&mut dyn FnMut(Span)->u64)->Result<Value,String> {Ok(match &value.kind{
 mir::TerminatorKind::Goto{target,loop_hint_attrs} if loop_hint_attrs.is_empty()=>json!({"kind":"goto","target":target.as_u32()}),
 mir::TerminatorKind::SwitchInt{discr,targets}=>{
  let shape=operand_shape(body,discr)?;
  let limit=if shape==json!({"kind":"boolean"}) {2} else if shape==json!({"kind":"uint","bits":32}) {1u128<<32} else {return Err("scalar CTFE switch type unsupported".into())};
  if targets.iter().any(|(value,_)|value>=limit) {return Err("scalar CTFE switch value exceeds source primitive width".into())}
  json!({"kind":"switch","operand":operand(body,discr,span)?,"cases":targets.iter().map(|(value,target)|json!({"value":value.to_string(),"target":target.as_u32()})).collect::<Vec<_>>(),"otherwise":targets.otherwise().as_u32()})},
 mir::TerminatorKind::Assert{cond,expected,msg,target,unwind:mir::UnwindAction::Unreachable}=>{
  if operand_shape(body,cond)?!=json!({"kind":"boolean"}) {return Err("scalar CTFE assertion condition must be bool".into())}
  let message=match &**msg {mir::AssertKind::Overflow(op,left,right)=>{
   let integer=json!({"kind":"uint","bits":32});
   if operand_shape(body,left)?!=integer || operand_shape(body,right)?!=integer {return Err("scalar CTFE overflow diagnostic operands must be u32".into())}
   let op=match op {mir::BinOp::Add=>"add",mir::BinOp::Sub=>"sub",_=>return Err("scalar CTFE overflow diagnostic op unsupported".into())};
   json!({"kind":"overflow","op":op,"left":operand(body,left,span)?,"right":operand(body,right,span)?})},mir::AssertKind::DivisionByZero(value)=>json!({"kind":"division_by_zero","operand":operand(body,value,span)?}),_=>return Err("scalar CTFE assertion diagnostic unsupported".into())};
  json!({"kind":"assert","condition":operand(body,cond,span)?,"expected":expected,"message":message,"target":target.as_u32(),"unwind":"unreachable"})},
 mir::TerminatorKind::UnwindResume=>json!({"kind":"resume"}),
 mir::TerminatorKind::Call{func,args,destination,target,unwind,call_source:mir::CallSource::Normal,fn_span}=>{
  let mir::Operand::Constant(function)=func else {return Err("indirect CTFE calls unsupported".into())};
  let ty::FnDef(definition,generics)=function.const_.ty().kind() else {return Err("call source is not FnDef".into())};
  if !definition.is_local() || !generics.bound_vars().is_empty() || !generics.skip_binder().is_empty() || !matches!(function.const_,mir::Const::Val(mir::ConstValue::ZeroSized,_)) {return Err("nonclosed raw FnDef source unsupported".into())}
  let signature=tcx.fn_sig(*definition).instantiate_identity().skip_norm_wip();
  if !signature.bound_vars().is_empty() || signature.skip_binder().abi()!=rustc_abi::ExternAbi::Rust || signature.skip_binder().c_variadic() || tcx.body_codegen_attrs(*definition).flags.contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::TRACK_CALLER) {return Err("call signature outside closed Rust ABI/no-track-caller source policy".into())}
  let target=target.ok_or("diverging source call unsupported")?;
  let unwind=match unwind {mir::UnwindAction::Unreachable=>json!({"kind":"unreachable"}),mir::UnwindAction::Cleanup(target)=>json!({"kind":"cleanup","target":target.as_u32()}),_=>return Err("call unwind source unsupported".into())};
  json!({"kind":"call","callee":identity(*definition),"type_arguments":[],"arguments":args.iter().map(|arg|operand(body,&arg.node,span)).collect::<Result<Vec<_>,String>>()?,"destination":place(body,*destination)?.0,"target":target.as_u32(),"unwind":unwind,"fn_span":span(*fn_span),"argument_spans":args.iter().map(|arg|span(arg.span)).collect::<Vec<_>>(),"call_source":"normal","function_user_type":function.user_ty.map(|index|index.as_u32()),"function_operand_span":span(function.span),"function_source_class":"literal_value","abi":"rust","track_caller":false})
 },
 mir::TerminatorKind::Return=>json!({"kind":"return"}),other=>return Err(format!("scalar CTFE terminator unsupported: {other:?}")),
})}

fn capture_impl<'tcx>(const_args:bool,tcx:TyCtxt<'tcx>,definition:DefId,promoted:Option<mir::Promoted>,body:&mir::Body<'tcx>,mut span:impl FnMut(Span)->u64)->Result<Value,String> {
 if body.source.def_id()!=definition || body.source.promoted!=promoted {return Err("CTFE raw source identity mismatch".into())}
 if !matches!(body.source.instance,ty::InstanceKind::Item(_)) || body.phase!=mir::MirPhase::Runtime(mir::RuntimePhase::PostCleanup) {return Err("scalar CTFE source requires Item mir_for_ctfe PostCleanup".into())}
 if body.coroutine.is_some() || body.spread_arg.is_some() || body.injection_phase.is_some() || body.source_scopes.iter().any(|scope|scope.inlined.is_some()) {return Err("scalar CTFE source has unsupported frame policy".into())}
 let generics=tcx.generics_of(definition);
 let mut constant_parameters=Vec::new();
 for index in 0..generics.count() {
  let parameter=generics.param_at(index,tcx);
  match parameter.kind {
   ty::GenericParamDefKind::Const{..} if const_args=>{
    let declared=tcx.type_of(parameter.def_id).instantiate_identity().skip_norm_wip();
    if !matches!(declared.kind(),ty::Uint(ty::UintTy::U32)) {return Err("const-args source requires u32 parameter declarations".into())}
    constant_parameters.push(json!({"index":index,"type":shape(declared)?}));
   },
   ty::GenericParamDefKind::Const{..}=>return Err("const parameter requires distinct const-args policy".into()),
   _ if const_args=>return Err("mixed type/region/constant parameter source unsupported".into()),
   _=>{},
  }
 }
 if const_args && constant_parameters.is_empty() {return Err("const-args source requires a constant parameter".into())}
 let required=body.required_consts.as_ref().ok_or("CTFE source lacks required-constant domain")?;
 if !definition.is_local() || promoted.is_some() || !body.user_type_annotations.is_empty() {return Err("calls policy requires local unpromoted PostCleanup source with cleared annotation table".into())}
 let info=|value:mir::SourceInfo,span:&mut dyn FnMut(Span)->u64|json!({"span":span(value.span),"scope":value.scope.as_u32()});
 let locals=body.local_decls.iter().map(|value|Ok(json!({"type":shape(value.ty)?,"source":info(value.source_info,&mut span),"mutable":value.mutability.is_mut()}))).collect::<Result<Vec<_>,String>>()?;
 let blocks=body.basic_blocks.iter().map(|block|{
  let statements=block.statements.iter().map(|value|Ok(json!({"source":info(value.source_info,&mut span),"kind":statement(body,value,&mut span)?}))).collect::<Result<Vec<_>,String>>()?;
  Ok(json!({"cleanup":block.is_cleanup,"statements":statements,"terminator":{"source":info(block.terminator().source_info,&mut span),"kind":terminator(tcx,body,block.terminator(),&mut span)?}}))
 }).collect::<Result<Vec<_>,String>>()?;
 let scopes=body.source_scopes.iter().map(|scope|{
  let lint=match &scope.local_data {mir::ClearCrossCrate::Set(data)=>json!({"owner":identity(data.lint_root.owner.def_id.to_def_id()),"local_id":data.lint_root.local_id.as_u32()}),mir::ClearCrossCrate::Clear=>Value::Null};
  json!({"span":span(scope.span),"parent":scope.parent_scope.map(|value|value.as_u32()),"lint_root":lint})
 }).collect::<Vec<_>>();
 let generics=tcx.generics_of(definition);let parameters=(0..generics.count()).map(|index|match generics.param_at(index,tcx).kind{ty::GenericParamDefKind::Lifetime=>"region",ty::GenericParamDefKind::Type{..}=>"type",ty::GenericParamDefKind::Const{..}=>"constant"}).collect::<Vec<_>>();
 let mut captured=json!({"definition":identity(definition),"source_role":"ctfe","promoted":promoted.map(|value|value.as_u32()),"policy":if const_args {"scalar_u32_const_args_v1"} else {"scalar_u32_calls_v1"},"phase":"runtime_post_cleanup","environment_recipe":{"kind":"declaration","owner":identity(definition),"mode":"post_analysis"},"parameters":parameters,"user_type_annotations":[],"required_consts":required.iter().map(|value|reference(value,&mut span)).collect::<Result<Vec<_>,String>>()?,"span":span(body.span),"arg_count":body.arg_count,"spread_arg":null,"locals":locals,"blocks":blocks,"source_scopes":scopes});
 if const_args {captured["constant_parameter_types"]=json!(constant_parameters);}
 Ok(captured)
}
pub(super) fn capture<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId,promoted:Option<mir::Promoted>,body:&mir::Body<'tcx>,span:impl FnMut(Span)->u64)->Result<Value,String> {
 capture_impl(false,tcx,definition,promoted,body,span)
}
pub(super) fn capture_const_args<'tcx>(tcx:TyCtxt<'tcx>,definition:DefId,promoted:Option<mir::Promoted>,body:&mir::Body<'tcx>,span:impl FnMut(Span)->u64)->Result<Value,String> {
 capture_impl(true,tcx,definition,promoted,body,span)
}
