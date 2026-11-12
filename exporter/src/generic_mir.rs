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
    tcx:TyCtxt<'tcx>, types:Vec<ty::Ty<'tcx>>, span:F,
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
    fn statement(&mut self, statement:&mir::Statement<'tcx>)->Result<String,String> {
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
fn supported_type(ty:ty::Ty<'_>)->bool {
    match ty.kind() {
        ty::Bool|ty::Char|ty::Int(_)|ty::Uint(_)|ty::Float(_)|ty::Never|ty::Str|ty::Param(_)|ty::Foreign(_)=>true,
        ty::Tuple(fields)=>fields.iter().all(supported_type),
        ty::RawPtr(inner,_)|ty::Ref(_,inner,_)|ty::Slice(inner)=>supported_type(*inner),
        ty::Array(inner,count)=>supported_type(*inner)&&supported_constant(*count),
        ty::Adt(_,args)=>supported_arguments(args),
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

pub fn capture<'tcx>(tcx:TyCtxt<'tcx>, body:&mir::Body<'tcx>,
    span:impl FnMut(Span)->u64)->Result<String,String> {
    if body.phase!=mir::MirPhase::Runtime(mir::RuntimePhase::Optimized) {
        return Err("copy template requires optimized runtime MIR".into());
    }
    if body.coroutine.is_some() || body.source_scopes.iter().any(|s|s.inlined.is_some()) {
        return Err("copy template excludes coroutine and inlined-source bodies".into());
    }
    if body.required_consts.as_ref().is_none_or(|constants|!constants.is_empty()) {
        return Err("copy template requires an empty explicit required-constants list".into());
    }
    let def=body.source.def_id();let generics=tcx.generics_of(def);
    let parameters=array((0..generics.count()).map(|index|quote(match generics.param_at(index,tcx).kind {
        ty::GenericParamDefKind::Lifetime=>"region",ty::GenericParamDefKind::Type{..}=>"type",
        ty::GenericParamDefKind::Const{..}=>"constant",
    })));
    let mut e=Encoder{tcx,types:Vec::new(),span};
    let locals=array(body.local_decls.iter().map(|local|e.ty(local.ty).to_string()));
    let mut blocks=Vec::new();
    for block in body.basic_blocks.iter() {
        let statements=array(block.statements.iter().map(|statement|e.statement(statement)).collect::<Result<Vec<_>,_>>()?);
        let terminator=e.terminator(block.terminator())?;
        blocks.push(format!("{{\"statements\":{statements},\"terminator\":{terminator},\"cleanup\":{}}}",block.is_cleanup));
    }
    if !e.types.iter().copied().all(|ty|supported_type(ty) || super::generic_mir_call::function_type_material(tcx,ty).is_ok()) {
        return Err("copy template source type family requires residual compiler instantiation".into());
    }
    let types=array(e.types.iter().map(|&ty|super::generic_material::type_tree(e.tcx,ty)).collect::<Result<Vec<_>,_>>()?);
    let spread=body.spread_arg.map(|id|id.as_u32().to_string()).unwrap_or_else(||"null".into());
    Ok(format!("{{\"parameters\":{parameters},\"types\":{types},\"skeleton\":{{\"phase\":\"runtime_optimized\",\"argument_count\":{},\"spread_argument\":{spread},\"locals\":{locals},\"blocks\":{}}}}}",body.arg_count,array(blocks)))
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
    if !supported_arguments(args) || !body.local_decls.iter().all(|local|supported_type(local.ty)) {
        return Err("source MIR interface requires the exact selected constructor family".into());
    }
    let instantiate=|ty|tcx.erase_and_anonymize_regions(
        ty::EarlyBinder::bind(tcx,ty).instantiate(tcx,args).skip_normalization());
    let arguments=body.args_iter().map(|local|(local,instantiate(body.local_decls[local].ty))).collect();
    Ok(Interface {argument_count:body.arg_count,spread_argument:body.spread_arg,
        arguments,return_type:instantiate(body.local_decls[mir::RETURN_PLACE].ty)})
}
