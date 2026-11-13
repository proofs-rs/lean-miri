//! Raw generic copy/aggregate MIR material. No instantiation, normalization,
//! layouts, ABI results or constant evaluation is queried by this module.
//! Unsupported instructions are an explicit different body-seed category.
use rustc_middle::{mir, ty::{self, TyCtxt}};
use rustc_span::Span;
use rustc_middle::ty::inherent::IntoKind;

fn quote(value: &str) -> String {
    let mut result=String::from("\"");
    for c in value.chars() {match c {
        '"'=>result.push_str("\\\""), '\\'=>result.push_str("\\\\"),
        '\n'=>result.push_str("\\n"), '\r'=>result.push_str("\\r"), '\t'=>result.push_str("\\t"),
        c if c<' '=>result.push_str(&format!("\\u{:04x}",c as u32)),
        c=>result.push(c),
    }}
    result.push('"');result
}
fn array(values: impl IntoIterator<Item=String>) -> String {
    format!("[{}]",values.into_iter().collect::<Vec<_>>().join(","))
}
fn object(kind:&str, fields:&str)->String {
    format!("{{\"kind\":{}{}{} }}",quote(kind),if fields.is_empty(){""}else{","},fields)
}
struct Encoder<'tcx,F> {
    tcx:TyCtxt<'tcx>, types:Vec<ty::Ty<'tcx>>, span:F, source_syntax:bool, allow_unevaluated:bool,
}
impl<'tcx,F:FnMut(Span)->u64> Encoder<'tcx,F> {
    fn ty(&mut self, ty:ty::Ty<'tcx>)->usize {
        if let Some(id)=self.types.iter().position(|&t|t==ty) {id}
        else {let id=self.types.len();self.types.push(ty);id}
    }
    fn source(&mut self, source:mir::SourceInfo)->String {
        format!("{{\"span\":{},\"scope\":{}}}",(self.span)(source.span),source.scope.as_u32())
    }
    fn place(&self, place:mir::Place<'tcx>)->Result<u32,String> {
        if !place.projection.is_empty() {return Err("copy template does not support projected places".into())}
        Ok(place.local.as_u32())
    }
    fn operand(&self, value:&mir::Operand<'tcx>)->Result<String,String> {
        Ok(match value {
            mir::Operand::Copy(place)=>object("copy",&format!("\"local\":{}",self.place(*place)?)),
            mir::Operand::Move(place)=>object("move",&format!("\"local\":{}",self.place(*place)?)),
            _=>return Err("copy template does not support constant/runtime-check operands".into()),
        })
    }
    fn rvalue(&mut self, value:&mir::Rvalue<'tcx>)->Result<String,String> {
        Ok(match value {
            mir::Rvalue::Use(value,retag)=>object("use",&format!("\"operand\":{},\"retag\":{}",self.operand(value)?,quote(match retag{mir::WithRetag::Yes=>"yes",mir::WithRetag::No=>"no"}))),
            mir::Rvalue::Aggregate(kind,values)=>{
                let values=array(values.iter().map(|value|self.operand(value)).collect::<Result<Vec<_>,_>>()?);
                match &**kind {
                    mir::AggregateKind::Tuple=>object("tuple",&format!("\"operands\":{values}")),
                    mir::AggregateKind::Array(ty)=>{let slot=self.ty(*ty);object("array",&format!("\"element\":{slot},\"operands\":{values}"))},
                    _=>return Err("copy template does not support this aggregate constructor".into()),
                }
            }
            _=>return Err("copy template does not support this rvalue".into()),
        })
    }
    fn source_place(&mut self, place:mir::Place<'tcx>)->Result<String,String> {
        let mut projections=Vec::new();
        for projection in place.projection.iter() {
            projections.push(match projection {
                mir::ProjectionElem::Deref=>object("deref",""),
                mir::ProjectionElem::Field(index,ty)=>{
                    let slot=self.ty(ty);object("field",&format!("\"index\":{},\"type\":{slot}",index.as_u32()))
                }
                mir::ProjectionElem::Downcast(name,index)=>object("downcast",&format!("\"name\":{},\"variant\":{}",
                    name.map(|name|quote(name.as_str())).unwrap_or_else(||"null".into()),index.as_u32())),
                mir::ProjectionElem::Index(local)=>object("index",&format!("\"local\":{}",local.as_u32())),
                mir::ProjectionElem::ConstantIndex{offset,min_length,from_end}=>object("constant_index",&format!("\"offset\":{offset},\"min_length\":{min_length},\"from_end\":{from_end}")),
                mir::ProjectionElem::Subslice{from,to,from_end}=>object("subslice",&format!("\"from\":{from},\"to\":{to},\"from_end\":{from_end}")),
                _=>return Err("source projection outside supported source grammar".into()),
            });
        }
        Ok(format!("{{\"local\":{},\"projection\":{}}}",place.local.as_u32(),array(projections)))
    }
    fn source_operand(&mut self, value:&mir::Operand<'tcx>)->Result<String,String> {
        Ok(match value {
            mir::Operand::Copy(place)=>object("copy",&format!("\"place\":{}",self.source_place(*place)?)),
            mir::Operand::Move(place)=>object("move",&format!("\"place\":{}",self.source_place(*place)?)),
            mir::Operand::Constant(constant)=>{
                let annotation=constant.user_ty.map(|index|index.as_u32());
                let annotation_fields=annotation.map(|index|format!(",\"user_type\":{{\"index\":{index},\"table_state\":\"cleared_post_borrowck\",\"entries\":[]}}" )).unwrap_or_default();
                if let mir::Const::Unevaluated(source,ty)=constant.const_ {
                    if !self.allow_unevaluated {return Err("raw Unevaluated source requires the explicit initial-query profile".into())}
                    let slot=self.ty(ty);let span=(self.span)(constant.span);
                    let arguments=array(source.args.iter().map(|argument|super::generic_material::argument(self.tcx,argument)).collect::<Result<Vec<_>,_>>()?);
                    let promoted=source.promoted.map(|index|index.as_u32().to_string()).unwrap_or_else(||"null".into());
                    let user_type=annotation.map(|index|format!("{{\"index\":{index},\"table_state\":\"cleared_post_borrowck\",\"entries\":[]}}")).unwrap_or_else(||"null".into());
                    object("unevaluated",&format!("\"type\":{slot},\"span\":{span},\"definition\":{{\"crate\":{},\"index\":{}}},\"arguments\":{arguments},\"promoted\":{promoted},\"user_type\":{user_type}",source.def.krate.as_u32(),source.def.index.as_u32()))
                } else {
                    let mir::Const::Val(value,ty)=constant.const_ else {
                        return Err("coroutine source constant requires raw Val, no CTFE evaluation".into());
                    };
                    let slot=self.ty(ty);let span=(self.span)(constant.span);
                    match value {
                        mir::ConstValue::ZeroSized=>object(if annotation.is_some(){"annotated_zero_sized"}else{"zero_sized"},&format!("\"type\":{slot},\"span\":{span}{annotation_fields}")),
                        mir::ConstValue::Scalar(scalar)=>{
                            let scalar=scalar.try_to_scalar_int().map_err(|_|"coroutine source pointer constant unsupported")?;
                            let bytes=scalar.size().bytes();let bits=scalar.to_bits_unchecked();
                            object(if annotation.is_some(){"annotated_scalar"}else{"scalar"},&format!("\"type\":{slot},\"span\":{span},\"bits\":\"{bits}\",\"bytes\":{bytes}{annotation_fields}"))
                        }
                        _=>return Err("coroutine source allocation constant unsupported".into()),
                    }
                }
            }
            _=>return Err("coroutine source runtime-check operand unsupported".into()),
        })
    }
    fn source_rvalue(&mut self, value:&mir::Rvalue<'tcx>)->Result<String,String> {
        Ok(match value {
            mir::Rvalue::Use(value,retag)=>object("use",&format!("\"operand\":{},\"retag\":{}",self.source_operand(value)?,quote(match retag{mir::WithRetag::Yes=>"yes",mir::WithRetag::No=>"no"}))),
            mir::Rvalue::Discriminant(place)=>object("discriminant",&format!("\"place\":{}",self.source_place(*place)?)),
            mir::Rvalue::Cast(kind,value,target)=>{
                let kind=match kind {mir::CastKind::IntToInt=>"int_to_int",mir::CastKind::FloatToInt=>"float_to_int",mir::CastKind::FloatToFloat=>"float_to_float",mir::CastKind::IntToFloat=>"int_to_float",mir::CastKind::PtrToPtr=>"ptr_to_ptr",mir::CastKind::FnPtrToPtr=>"fn_ptr_to_ptr",mir::CastKind::PointerExposeProvenance=>"pointer_expose_provenance",mir::CastKind::PointerWithExposedProvenance=>"pointer_with_exposed_provenance",mir::CastKind::Transmute=>"transmute",_=>return Err("source cast kind outside supported source grammar".into())};
                let target=self.ty(*target);object("cast",&format!("\"cast\":{},\"operand\":{},\"target\":{target}",quote(kind),self.source_operand(value)?))
            }
            mir::Rvalue::Ref(region,borrow,place)=>{
                if !matches!(region.kind(),ty::RegionKind::ReErased) {return Err("source Ref requires explicit raw erased region".into())}
                let borrow=match borrow {mir::BorrowKind::Shared=>"shared",mir::BorrowKind::Mut{kind:mir::MutBorrowKind::Default}=>"mut_default",mir::BorrowKind::Mut{kind:mir::MutBorrowKind::TwoPhaseBorrow}=>"mut_two_phase",mir::BorrowKind::Mut{kind:mir::MutBorrowKind::ClosureCapture}=>"mut_closure_capture",mir::BorrowKind::Fake(mir::FakeBorrowKind::Shallow)=>"fake_shallow",mir::BorrowKind::Fake(mir::FakeBorrowKind::Deep)=>"fake_deep"};
                object("reference",&format!("\"region\":\"erased\",\"borrow\":{},\"place\":{}",quote(borrow),self.source_place(*place)?))
            }
            mir::Rvalue::RawPtr(kind,place)=>{
                let kind=match kind {mir::RawPtrKind::Const=>"const",mir::RawPtrKind::Mut=>"mut",mir::RawPtrKind::FakeForPtrMetadata=>"fake_for_metadata"};
                object("raw_pointer",&format!("\"pointer\":{},\"place\":{}",quote(kind),self.source_place(*place)?))
            }

            mir::Rvalue::Aggregate(kind,values)=>{
                let operands=array(values.iter().map(|value|self.source_operand(value)).collect::<Result<Vec<_>,_>>()?);
                match &**kind {
                    mir::AggregateKind::Tuple=>object("tuple",&format!("\"operands\":{operands}")),
                    mir::AggregateKind::Adt(def,variant,args,user,active)=>{
                        if user.is_some() || active.is_some() {return Err("coroutine source annotated/union aggregate unsupported".into())}
                        let ty=ty::Ty::new_adt(self.tcx,self.tcx.adt_def(*def),args);
                        let slot=self.ty(ty);
                        object("adt",&format!("\"type\":{slot},\"variant\":{},\"operands\":{operands}",variant.as_u32()))
                    }
                    _=>return Err("coroutine source aggregate unsupported".into()),
                }
            }
            _=>return Err("coroutine source rvalue unsupported".into()),
        })
    }
    fn source_unwind(value:mir::UnwindAction)->Result<String,String> {
        Ok(match value {
            mir::UnwindAction::Continue=>object("continue",""),
            mir::UnwindAction::Unreachable=>object("unreachable",""),
            mir::UnwindAction::Cleanup(target)=>object("cleanup",&format!("\"target\":{}",target.as_u32())),
            _=>return Err("coroutine source terminate unwind unsupported".into()),
        })
    }
    fn source_statement(&mut self, statement:&mir::Statement<'tcx>)->Result<String,String> {
        let kind=match &statement.kind {
            mir::StatementKind::Assign(pair)=>object("source_assign",&format!("\"place\":{},\"value\":{}",self.source_place(pair.0)?,self.source_rvalue(&pair.1)?)),
            mir::StatementKind::PlaceMention(place)=>object("source_place_mention",&format!("\"place\":{}",self.source_place(**place)?)),
            mir::StatementKind::SetDiscriminant{place,variant_index}=>object("set_discriminant",&format!("\"place\":{},\"variant\":{}",self.source_place(**place)?,variant_index.as_u32())),
            mir::StatementKind::StorageLive(local)=>object("storage_live",&format!("\"local\":{}",local.as_u32())),
            mir::StatementKind::StorageDead(local)=>object("storage_dead",&format!("\"local\":{}",local.as_u32())),
            mir::StatementKind::Nop=>object("nop",""),
            _=>return Err("coroutine source statement unsupported".into()),
        };
        Ok(format!("{{\"source\":{},\"kind\":{kind}}}",self.source(statement.source_info)))
    }
    fn source_terminator(&mut self, terminator:&mir::Terminator<'tcx>)->Result<String,String> {
        let kind=match &terminator.kind {
            mir::TerminatorKind::Return=>object("return",""),
            mir::TerminatorKind::Unreachable=>object("unreachable",""),
            mir::TerminatorKind::UnwindResume=>object("unwind_resume",""),
            mir::TerminatorKind::Goto{target,loop_hint_attrs}=>{
                if !loop_hint_attrs.is_empty(){return Err("coroutine source loop hints unsupported".into())}
                object("goto",&format!("\"target\":{}",target.as_u32()))
            }
            mir::TerminatorKind::SwitchInt{discr,targets}=>{
                let cases=array(targets.iter().map(|(value,target)|format!("{{\"value\":\"{value}\",\"target\":{}}}",target.as_u32())));
                object("source_switch",&format!("\"operand\":{},\"cases\":{cases},\"otherwise\":{}",self.source_operand(discr)?,targets.otherwise().as_u32()))
            }
            mir::TerminatorKind::Call{func,args,destination,target,unwind,call_source,fn_span}=>{
                super::generic_mir_call::callee(self.tcx,func)?;
                if !matches!(call_source,mir::CallSource::Normal) {return Err("source call kind outside normal source".into())}
                let mir::Operand::Constant(constant)=func else {unreachable!()};
                let function=self.ty(constant.const_.ty());let span=(self.span)(constant.span);let function_span=(self.span)(*fn_span);
                let arguments=array(args.iter().map(|argument|Ok(format!("{{\"span\":{},\"operand\":{}}}",(self.span)(argument.span),self.source_operand(&argument.node)?))).collect::<Result<Vec<_>,String>>()?);
                let target=target.map(|value|value.as_u32().to_string()).unwrap_or_else(||"null".into());
                object("source_call",&format!("\"function\":{function},\"constant_span\":{span},\"arguments\":{arguments},\"place\":{},\"target\":{target},\"unwind\":{},\"function_span\":{function_span}",self.source_place(*destination)?,Self::source_unwind(*unwind)?))
            }
            mir::TerminatorKind::Assert{cond,expected,msg,target,unwind}=>{
                let (message,kind)=match &**msg {
                    mir::AssertKind::ResumedAfterReturn(kind)=>("return",kind),
                    mir::AssertKind::ResumedAfterPanic(kind)=>("panic",kind),
                    mir::AssertKind::ResumedAfterDrop(kind)=>("drop",kind),
                    _=>return Err("coroutine source assertion diagnostic unsupported".into()),
                };
                let coroutine=match *kind {
                    rustc_hir::CoroutineKind::Coroutine(movability)=>object("coroutine",&format!("\"movability\":{}",quote(match movability {
                        rustc_hir::Movability::Static=>"static",rustc_hir::Movability::Movable=>"movable" }))),
                    rustc_hir::CoroutineKind::Desugared(desugaring,source)=>object("desugared",&format!("\"desugaring\":{},\"source\":{}",
                        quote(match desugaring {rustc_hir::CoroutineDesugaring::Async=>"async",rustc_hir::CoroutineDesugaring::Gen=>"gen",rustc_hir::CoroutineDesugaring::AsyncGen=>"async_gen"}),
                        quote(match source {rustc_hir::CoroutineSource::Block=>"block",rustc_hir::CoroutineSource::Closure=>"closure",rustc_hir::CoroutineSource::Fn=>"function"}))),
                };
                object("assert_resume",&format!("\"operand\":{},\"expected\":{expected},\"message\":{},\"coroutine\":{coroutine},\"target\":{},\"unwind\":{}",self.source_operand(cond)?,quote(message),target.as_u32(),Self::source_unwind(*unwind)?))
            }
            mir::TerminatorKind::Drop{place,target,unwind,replace,drop:async_drop}=>{
                let async_drop=async_drop.map(|v|v.as_u32().to_string()).unwrap_or_else(||"null".into());
                object("source_drop",&format!("\"place\":{},\"target\":{},\"unwind\":{},\"replace\":{replace},\"async_drop\":{async_drop}",self.source_place(*place)?,target.as_u32(),Self::source_unwind(*unwind)?))
            }
            _=>return Err("coroutine source terminator unsupported".into()),
        };
        Ok(format!("{{\"source\":{},\"kind\":{kind}}}",self.source(terminator.source_info)))
    }
    fn statement(&mut self, statement:&mir::Statement<'tcx>)->Result<String,String> {
        if self.source_syntax {return self.source_statement(statement)}
        let kind=match &statement.kind {
            mir::StatementKind::Assign(pair)=>object("assign",&format!("\"destination\":{},\"value\":{}",self.place(pair.0)?,self.rvalue(&pair.1)?)),
            mir::StatementKind::StorageLive(local)=>object("storage_live",&format!("\"local\":{}",local.as_u32())),
            mir::StatementKind::StorageDead(local)=>object("storage_dead",&format!("\"local\":{}",local.as_u32())),
            mir::StatementKind::PlaceMention(place)=>object("place_mention",&format!("\"local\":{}",self.place(**place)?)),
            mir::StatementKind::Nop=>object("nop",""),
            _=>return Err("copy template does not support this statement".into()),
        };
        Ok(format!("{{\"source\":{},\"kind\":{kind}}}",self.source(statement.source_info)))
    }
    fn terminator(&mut self, terminator:&mir::Terminator<'tcx>)->Result<String,String> {
        if self.source_syntax {return self.source_terminator(terminator)}
        let kind=match &terminator.kind {
            mir::TerminatorKind::Call{func,args,destination,target,unwind,call_source,fn_span}=>{
                super::generic_mir_call::callee(self.tcx,func)?;
                if !matches!(unwind,mir::UnwindAction::Unreachable)
                    || !matches!(call_source,mir::CallSource::Normal) {
                    return Err("ordinary source call requires normal source and unreachable unwind".into());
                }
                let mir::Operand::Constant(constant)=func else {unreachable!()};
                let function_type=self.ty(constant.const_.ty());
                let constant_span=(self.span)(constant.span);
                let function_span=(self.span)(*fn_span);
                let destination=self.place(*destination)?;
                let arguments=array(args.iter().map(|argument|Ok(format!("{{\"span\":{},\"operand\":{}}}",
                    (self.span)(argument.span),self.operand(&argument.node)?))).collect::<Result<Vec<_>,String>>()?);
                let target=target.map(|target|target.as_u32().to_string()).unwrap_or_else(||"null".into());
                object("call",&format!("\"function_type\":{function_type},\"constant_span\":{constant_span},\"arguments\":{arguments},\"destination\":{destination},\"target\":{target},\"unwind\":\"unreachable\",\"call_source\":\"normal\",\"function_span\":{function_span}"))
            }
            mir::TerminatorKind::Return=>object("return",""),
            mir::TerminatorKind::Unreachable=>object("unreachable",""),
            mir::TerminatorKind::Goto{target,loop_hint_attrs}=>{
                if !loop_hint_attrs.is_empty(){return Err("copy template requires absent loop hints".into())}
                object("goto",&format!("\"target\":{}",target.as_u32()))
            }
            mir::TerminatorKind::SwitchInt{discr,targets}=>{
                let cases=array(targets.iter().map(|(value,target)|format!("{{\"value\":{value},\"target\":{}}}",target.as_u32())));
                object("switch",&format!("\"operand\":{},\"cases\":{cases},\"otherwise\":{}",self.operand(discr)?,targets.otherwise().as_u32()))
            }
            _=>return Err("copy template does not support this terminator".into()),
        };
        Ok(format!("{{\"source\":{},\"kind\":{kind}}}",self.source(terminator.source_info)))
    }
}

/// Constructor families supported by the production generic tree bridge.
/// Eligibility is source-derived, never selected by comparing monomorphic MIR
/// or layout results. Other families remain an explicit material-body category.
pub(super) fn supported_type(ty:ty::Ty<'_>)->bool {
    match ty.kind() {
        ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Float(_)|ty::Never|ty::Str|ty::Param(_)|ty::Foreign(_)=>true,
        ty::Tuple(fields)=>fields.iter().all(supported_type),
        ty::RawPtr(inner,_)|ty::Ref(_,inner,_)|ty::Slice(inner)=>supported_type(*inner),
        ty::Array(inner,count)=>supported_type(*inner)&&supported_constant(*count),
        ty::Adt(_,args)|ty::Coroutine(_,args)=>supported_arguments(args),
        ty::FnPtr(types,header)=>{
            let signature=types.with(*header);
            signature.bound_vars().is_empty() &&
                signature.skip_binder().inputs_and_output.iter().all(supported_type)
        }
        _=>false,
    }
}
fn supported_constant(value:ty::Const<'_>)->bool {
    match value.kind() {
        ty::ConstKind::Param(_)=>true,
        ty::ConstKind::Value(value)=>supported_type(value.ty),
        _=>false,
    }
}
pub fn supported_arguments(args:ty::GenericArgsRef<'_>)->bool {
    args.iter().all(|arg|match arg.kind() {
        ty::GenericArgKind::Type(ty)=>supported_type(ty),
        ty::GenericArgKind::Const(value)=>supported_constant(value),
        ty::GenericArgKind::Lifetime(_)=>true,
    })
}

/// Classify the exact ported category before serialization. Once true, any
/// capture/instantiation failure is an error, never a monomorphic-body fallback.
pub fn eligible<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, args:ty::GenericArgsRef<'tcx>)->bool {
    if body.coroutine.is_some() {
        return supported_arguments(args) && capture(tcx,body,|_|0).is_ok();
    }
    fn place(value:mir::Place<'_>)->bool {value.projection.is_empty()}
    fn operand(value:&mir::Operand<'_>)->bool {match value {
        mir::Operand::Copy(value)|mir::Operand::Move(value)=>place(*value), _=>false,
    }}
    fn rvalue(value:&mir::Rvalue<'_>)->bool {match value {
        mir::Rvalue::Use(value,_)=>operand(value),
        mir::Rvalue::Aggregate(kind,values)=>
            matches!(&**kind,mir::AggregateKind::Tuple) && values.iter().all(operand)
            || matches!(&**kind,mir::AggregateKind::Array(ty) if supported_type(*ty)) && values.iter().all(operand),
        _=>false,
    }}
    if body.phase!=mir::MirPhase::Runtime(mir::RuntimePhase::Optimized)
        || body.coroutine.is_some() || body.source_scopes.iter().any(|s|s.inlined.is_some())
        || body.required_consts.as_ref().is_none_or(|constants|!constants.is_empty())
        || !supported_arguments(args) || !body.local_decls.iter().all(|local|supported_type(local.ty)) {
        return false;
    }
    body.basic_blocks.iter().all(|block| {
        block.statements.iter().all(|statement|match &statement.kind {
            mir::StatementKind::Assign(pair)=>place(pair.0)&&rvalue(&pair.1),
            mir::StatementKind::StorageLive(_)|mir::StatementKind::StorageDead(_)|mir::StatementKind::Nop=>true,
            mir::StatementKind::PlaceMention(value)=>place(**value),_=>false,
        }) && match &block.terminator().kind {
            mir::TerminatorKind::Return|mir::TerminatorKind::Unreachable=>true,
            mir::TerminatorKind::Goto{loop_hint_attrs,..}=>loop_hint_attrs.is_empty(),
            mir::TerminatorKind::SwitchInt{discr,..}=>operand(discr),
            // Source callee identity and type arguments are reconstructed on
            // demand; the existing instance/ABI graph remains explicit residual.
            mir::TerminatorKind::Call{func,args,destination,unwind,call_source,..}=>
                super::generic_mir_call::callee(tcx,func).is_ok()
                && args.iter().all(|argument|operand(&argument.node))
                && place(*destination)
                && matches!(unwind,mir::UnwindAction::Unreachable)
                && matches!(call_source,mir::CallSource::Normal),
            _=>false,
        }
    })
}

/// Optional evidence for the two explicit executable-body acquisition sites
/// in the producer. Auxiliary snapshot normalization is a separate metadata
/// operation and is not an executable-body acquisition.
pub fn source_query_trace(route:&str,queried:bool,instance:ty::Instance<'_>) {
    if std::env::var_os("LEAN_MIRI_MIR_SOURCE_TRACE").is_some() {
        let definition=instance.def.def_id();
        eprintln!("LEAN_MIRI_MIR_SOURCE_QUERY\t{route}\tqueried={queried}\t{}:{}\t{instance:?}",definition.krate.as_u32(),definition.index.as_u32());
    }
}

/// Explicit raw source syntax category. The root selector decides admission
/// before any closed-body acquisition; selected capture errors propagate.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Category { Copy, Extended }

pub fn source_category<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, args:ty::GenericArgsRef<'tcx>)->Option<Category> {
    if eligible(tcx,body,args) {
        return Some(if body.coroutine.is_some(){Category::Extended}else{Category::Copy});
    }
    if supported_arguments(args) && capture_extended(tcx,body,|_|0).is_ok() {
        Some(Category::Extended)
    } else {None}
}
pub fn capture_category<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, category:Category,
    span:impl FnMut(Span)->u64)->Result<String,String> {
    match category {
        Category::Copy=>{
            if body.coroutine.is_some() {return Err("copy source category cannot contain coroutine metadata".into())}
            capture_mode(tcx,body,span,false,false)
        }
        Category::Extended=>capture_extended(tcx,body,span),
    }
}

pub fn capture<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, span:impl FnMut(Span)->u64)->Result<String,String> {
    capture_mode(tcx,body,span,body.coroutine.is_some(),false)
}
pub fn capture_extended<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>, span:impl FnMut(Span)->u64)->Result<String,String> {
    capture_mode(tcx,body,span,true,false)
}
fn capture_mode<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>,
    span:impl FnMut(Span)->u64,source_syntax:bool,allow_unevaluated:bool)->Result<String,String> {
    if body.phase!=mir::MirPhase::Runtime(mir::RuntimePhase::Optimized) {
        return Err("copy template requires optimized runtime MIR".into());
    }
    if body.source_scopes.iter().any(|s|s.inlined.is_some()) {
        return Err("source template excludes inlined-source bodies".into());
    }
    if body.required_consts.as_ref().is_none_or(|constants|!constants.is_empty()) {
        return Err("copy template requires an empty explicit required-constants list".into());
    }
    // Runtime optimized source is post-CleanupPostBorrowck. ConstOperand
    // retains a phase-stale user_ty breadcrumb even though the table is empty.
    // Nonempty canonical tables require a different complete source category.
    if source_syntax && (!body.user_type_annotations.is_empty() || body.local_decls.iter().any(|local|local.user_ty.is_some())) {
        return Err("source annotation table was not cleared post borrowck".into());
    }
    let def=body.source.def_id();let generics=tcx.generics_of(def);
    let parameters=array((0..generics.count()).map(|index|quote(match generics.param_at(index,tcx).kind {
        ty::GenericParamDefKind::Lifetime=>"region",ty::GenericParamDefKind::Type{..}=>"type",
        ty::GenericParamDefKind::Const{..}=>"constant",
    })));
    let mut e=Encoder{tcx,types:Vec::new(),span,source_syntax,allow_unevaluated};
    let locals=array(body.local_decls.iter().map(|local|e.ty(local.ty).to_string()));
    let mut blocks=Vec::new();
    for block in body.basic_blocks.iter() {
        let statements=array(block.statements.iter().map(|statement|e.statement(statement)).collect::<Result<Vec<_>,_>>()?);
        let terminator=e.terminator(block.terminator())?;
        blocks.push(format!("{{\"statements\":{statements},\"terminator\":{terminator},\"cleanup\":{}}}",block.is_cleanup));
    }
    if !e.types.iter().copied().all(|ty|supported_source_type(tcx,ty)) {
        return Err("copy template source type family requires residual compiler instantiation".into());
    }
    let types=array(e.types.iter().map(|&ty|super::generic_material::type_tree(e.tcx,ty)).collect::<Result<Vec<_>,_>>()?);
    let spread=body.spread_arg.map(|id|id.as_u32().to_string()).unwrap_or_else(||"null".into());
    Ok(format!("{{\"parameters\":{parameters},\"types\":{types},\"skeleton\":{{\"phase\":\"runtime_optimized\",\"argument_count\":{},\"spread_argument\":{spread},\"locals\":{locals},\"blocks\":{}}}}}",body.arg_count,array(blocks)))
}

/// The exact raw source type admission used by executable capture and its
/// interface-only consumer. FnDef slots retain ordinary callable declaration
/// syntax; neither path substitutes a closed body or acquires an ABI answer.
fn supported_source_type<'tcx>(tcx:TyCtxt<'tcx>, value:ty::Ty<'tcx>)->bool {
    supported_type(value) || super::generic_mir_call::function_type_material(tcx,value).is_ok()
}

/// Argument/return type dependencies for the remaining covariance leaf. Never
/// reconstruct an executable body merely to discover its interface types.
pub struct Interface<'tcx> {
    pub argument_count:usize,
    pub spread_argument:Option<mir::Local>,
    pub arguments:Vec<(mir::Local,ty::Ty<'tcx>)>,
    pub return_type:ty::Ty<'tcx>,
}

pub fn interface<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,
    args:ty::GenericArgsRef<'tcx>)->Result<Interface<'tcx>,String> {
    if !supported_arguments(args) || !body.local_decls.iter().all(|local|supported_source_type(tcx,local.ty)) {
        return Err("source MIR interface requires the exact selected constructor family".into());
    }
    let instantiate=|ty|tcx.erase_and_anonymize_regions(
        ty::EarlyBinder::bind(tcx,ty).instantiate(tcx,args).skip_normalization());
    let arguments=body.args_iter().map(|local|(local,instantiate(body.local_decls[local].ty))).collect();
    Ok(Interface {argument_count:body.arg_count,spread_argument:body.spread_arg,
        arguments,return_type:instantiate(body.local_decls[mir::RETURN_PLACE].ty)})
}

/// Initial-query profile only. Legacy source admission retains its prior
/// categories, so adding raw syntax cannot silently disable old provider paths.
pub fn source_category_raw<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,args:ty::GenericArgsRef<'tcx>)->Option<Category> {
    source_category(tcx,body,args).or_else(|| {
        if supported_arguments(args) && capture_mode(tcx,body,|_|0,true,true).is_ok() {Some(Category::Extended)} else {None}
    })
}
pub fn capture_category_raw<'tcx>(tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>,category:Category,
    span:impl FnMut(Span)->u64)->Result<String,String> {
    match category {Category::Copy=>capture_mode(tcx,body,span,false,false),Category::Extended=>capture_mode(tcx,body,span,true,true)}
}
