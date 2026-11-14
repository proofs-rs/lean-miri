//! Bounded source-only dependency capture. A missing/unsupported source remains
//! unavailable to the CTFE reader; this collector does not grant query admission.
use rustc_hir::{def::DefKind,def_id::DefId};
use rustc_middle::{mir,ty::{self,TyCtxt}};
use rustc_middle::mir::visit::Visitor;
use serde_json::Value;
use super::{ExportContext,ctfe_body_source,ctfe_scalar_source,ctfe_calls_source,def_json,span_json};

#[derive(Default)]
pub(super) struct Catalog {
    /// Reserve before walking dependencies; recursive source calls terminate.
    seen: std::collections::HashSet<ctfe_body_source::TemplateKey>,
    sources: Vec<Value>,
    /// Capture failures are distinct from successful empty source bodies.
    unavailable: Vec<(ctfe_body_source::TemplateKey,String)>,
}
impl Catalog {
    pub(super) fn demanded_definitions(&self)->Result<Vec<DefId>,String> {
        let mut values=Vec::new();
        // Close only retained physical-u64 source syntax. Unavailable or legacy
        // scalar/calls candidates must not amplify the raw template worklist.
        for source in &self.sources {
            if source.get("policy").and_then(Value::as_str)==Some("u64_physical_constants_v1") {
                super::generic_definition_references(source,&mut values)?;
            }
        }
        values.sort_by_key(|id|(id.krate.as_u32(),id.index.as_u32()));
        values.dedup();Ok(values)
    }
    pub(super) fn finish(self)->Vec<Value> {
        // The typed scalar catalogue deliberately contains only complete sources.
        // Missing entries are rejected by lookup, never used as query answers.
        self.sources
    }
}
#[derive(Default)]
struct Dependencies {
    constants:Vec<(DefId,Option<mir::Promoted>)>,
    calls:Vec<DefId>,
}
impl<'tcx> Visitor<'tcx> for Dependencies {
    fn visit_const_operand(&mut self,value:&mir::ConstOperand<'tcx>,location:mir::Location) {
        if let mir::Const::Unevaluated(source,_)=value.const_ {
            self.constants.push((source.def,source.promoted));
        }
        self.super_const_operand(value,location);
    }
    fn visit_terminator(&mut self,value:&mir::Terminator<'tcx>,location:mir::Location) {
        if let mir::TerminatorKind::Call {func:mir::Operand::Constant(function),..}=&value.kind {
            if let ty::FnDef(definition,_)=function.const_.ty().kind() {self.calls.push(*definition);}
        }
        self.super_terminator(value,location);
    }
}
fn has_body(tcx:TyCtxt<'_>,definition:DefId)->bool {
    if let Some(available)=super::ctfe_type_const_source::const_body_available(tcx,definition) {return available}
    match tcx.def_kind(definition) {
        DefKind::AssocConst|DefKind::AssocFn if !tcx.associated_item(definition).defaultness(tcx).has_value()=>return false,
        _=>{},
    }
    // Avoid asking for MIR of required trait members or foreign declarations.
    super::has_local_hir_body(tcx,definition) || tcx.is_mir_available(definition)
}
fn const_callable(tcx:TyCtxt<'_>,definition:DefId)->bool {
    matches!(tcx.def_kind(definition),DefKind::Fn|DefKind::AssocFn)
        && matches!(tcx.constness(definition),rustc_hir::Constness::Const {..})
}
pub(super) fn demand_reachable<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,body:&mir::Body<'tcx>)->Result<(),String> {
    if const_callable(tcx,body.source.def_id()) || body.source.promoted.is_some() ||
        matches!(tcx.def_kind(body.source.def_id()),DefKind::Const|DefKind::AssocConst|DefKind::AnonConst|DefKind::Static {..}) {
        demand(context,tcx,body.source.def_id(),body.source.promoted)?;
    }
    let mut dependencies=Dependencies::default();dependencies.visit_body(body);
    for (definition,promoted) in dependencies.constants {demand(context,tcx,definition,promoted)?;}
    for definition in dependencies.calls {
        if const_callable(tcx,definition) {demand(context,tcx,definition,None)?;}
    }
    Ok(())
}
pub(super) fn demand<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,definition:DefId,promoted:Option<mir::Promoted>)->Result<(),String> {
    let key=ctfe_body_source::TemplateKey {definition,promoted,role:ctfe_body_source::Role::Ctfe};
    if !context.ctfe_scalar_sources.seen.insert(key) {return Ok(())}
    def_json(context,definition);
    if !has_body(tcx,definition) {
        let reason = "raw CTFE source has no available body";
        if std::env::var_os("LEAN_MIRI_TRACE_CTFE_SOURCE").is_some() {
            eprintln!("lean_miri_ctfe_source unavailable={} promoted={promoted:?} reason={reason}",tcx.def_path_str(definition));
        }
        context.ctfe_scalar_sources.unavailable.push((key,reason.into()));
        return Ok(())
    }
    let body=if let Some(index)=promoted {
        let bodies=tcx.promoted_mir(definition);
        let Some(body)=bodies.get(index) else {return Err("CTFE source promoted identity absent".into())};body
    } else {tcx.mir_for_ctfe(definition)};
    super::ensure_untainted_mir(body)?;
    for scope in body.source_scopes.iter() {
        if let mir::ClearCrossCrate::Set(data)=&scope.local_data {def_json(context,data.lint_root.owner.def_id.to_def_id());}
    }
    match ctfe_scalar_source::capture(tcx,definition,promoted,body,|span|span_json(context,tcx,span))
        .or_else(|_|ctfe_calls_source::capture(tcx,definition,promoted,body,|span|span_json(context,tcx,span)))
        .or_else(|_|ctfe_calls_source::capture_const_args(tcx,definition,promoted,body,|span|span_json(context,tcx,span)))
        .or_else(|_| {
            if promoted.is_some() {return Err("u64 physical type-const policy excludes promoted bodies".into())}
            super::ctfe_type_const_source::capture(tcx,definition,body,|span|span_json(context,tcx,span))
        }) {
        Ok(source)=>context.ctfe_scalar_sources.sources.push(source),
        Err(reason)=>{
            if std::env::var_os("LEAN_MIRI_TRACE_CTFE_SOURCE").is_some() {
                eprintln!("lean_miri_ctfe_source unavailable={} promoted={promoted:?} reason={reason}",tcx.def_path_str(definition));
            }
            context.ctfe_scalar_sources.unavailable.push((key,reason));
        },
    }
    // Walk raw MIR even when this bounded frame policy cannot execute its root.
    // No producer Instance::try_resolve, const evaluation, layout or ABI query.
    demand_reachable(context,tcx,body)
}
