//! Source facts only: no layout, ABI or compiler query answers.
use rustc_middle::{mir, ty::TyCtxt};
use rustc_span::Pos;
use serde_json::{json, Value};

type SpanIds = std::collections::HashMap<rustc_span::Span, usize>;

fn span(ids: &mut SpanIds, tcx: TyCtxt<'_>, value: rustc_span::Span) -> Value {
    let next = ids.len();
    let id = *ids.entry(value).or_insert(next);
    let map = tcx.sess.source_map();
    let start = map.lookup_char_pos(value.lo());
    let end = map.lookup_char_pos(value.hi());
    json!({"span_id":id,"parent_local_definition":value.parent().map(|d|d.local_def_index.as_u32()),"is_dummy":value.is_dummy(),"lo":value.lo().0,"hi":value.hi().0,
        "ctxt":format!("{:?}",value.ctxt()),"file":format!("{:?}",start.file.name),
        "start":{"line":start.line,"column":start.col.to_usize()},
        "end":{"line":end.line,"column":end.col.to_usize()}})
}
fn info(ids: &mut SpanIds, tcx: TyCtxt<'_>, value: mir::SourceInfo) -> Value {
    json!({"span":span(ids,tcx,value.span),"scope":value.scope.as_u32()})
}
fn backtraces(ids: &mut SpanIds, tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> Vec<Value> {
    // Same body-relative hygiene collapse as schema12 backtrace_spans_json.
    let mut spans = vec![body.span, tcx.def_span(body.source.def_id())];
    spans.extend(body.local_decls.iter().map(|l| l.source_info.span));
    for block in body.basic_blocks.iter() {
        spans.extend(block.statements.iter().map(|s| s.source_info.span));
        if let Some(t) = &block.terminator { spans.push(t.source_info.span); }
    }
    let mut seen = std::collections::HashSet::new();
    spans.into_iter().filter(|s| seen.insert(*s)).map(|original| {
        let collapsed = rustc_span::hygiene::walk_chain_collapsed(original, body.span);
        let position = tcx.sess.source_map().lookup_char_pos(collapsed.lo());
        json!({"span":span(ids,tcx,original),"source_position":{
            "byte_position":collapsed.lo().0,"line":position.line,
            "zero_based_char_column":position.col.0,
            "filename":position.file.name.prefer_remapped_unconditionally().to_string()}})
    }).collect()
}
pub(super) fn capture(tcx: TyCtxt<'_>, body: &mir::Body<'_>) -> Value {
    struct ConstantSpans { values: Vec<rustc_span::Span> }
    impl<'tcx> mir::visit::Visitor<'tcx> for ConstantSpans {
        fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _: mir::Location) {
            self.values.push(constant.span);
        }
    }
    let mut constant_spans = ConstantSpans { values: Vec::new() };
    mir::visit::Visitor::visit_body(&mut constant_spans, body);
    let mut ids = SpanIds::new();
    // Storage markers remain executable MIR. Whether a local is always live
    // can be derived from their absence, as in pinned interpret/stack.rs.
    let body_span = span(&mut ids,tcx,body.span);
    let backtrace_spans = backtraces(&mut ids,tcx,body);
    let definition_span = span(&mut ids,tcx,tcx.def_span(body.source.def_id()));
    let locals = body.local_decls.iter().map(|l|json!({"mutable":l.mutability.is_mut(),
        "source_info":info(&mut ids,tcx,l.source_info)})).collect::<Vec<_>>();
    let scopes = body.source_scopes.iter().map(|s|json!({"span":span(&mut ids,tcx,s.span),
        "parent":s.parent_scope.map(|p|p.as_u32()),
        "inlined_parent":s.inlined_parent_scope.map(|p|p.as_u32())})).collect::<Vec<_>>();
    let blocks = body.basic_blocks.iter().map(|b|json!({
        "statements":b.statements.iter().map(|s|info(&mut ids,tcx,s.source_info)).collect::<Vec<_>>(),
        "terminator":info(&mut ids,tcx,b.terminator().source_info)})).collect::<Vec<_>>();
    // Argument and function spans are independent rustc Span identities. They
    // share this body's exact namespace with ordinary source locations.
    let call_spans = body.basic_blocks.iter().map(|b|match &b.terminator().kind {
        mir::TerminatorKind::Call {func,args,fn_span,..} => json!({
            "function":span(&mut ids,tcx,*fn_span),
            "function_operand":match func {
                mir::Operand::Constant(c) => Some(span(&mut ids,tcx,c.span)),
                _ => None,
            },
            "arguments":args.iter().map(|arg|span(&mut ids,tcx,arg.span)).collect::<Vec<_>>()
        }),
        _ => Value::Null,
    }).collect::<Vec<_>>();
    let additional_spans = constant_spans.values.iter().map(|value|span(&mut ids,tcx,*value)).collect::<Vec<_>>();
    json!({"span":body_span,"additional_spans":additional_spans,
        "backtrace_spans":backtrace_spans,
        "definition_span":definition_span,
        "phase":crate::mir_phase_json(body.phase),
        "injection_phase":body.injection_phase.map(crate::mir_phase_json),
        "locals":locals,"scopes":scopes,"blocks":blocks,
        "call_spans":call_spans})
}

// eval.rs constructs InterpCx with the actual compiler DUMMY_SP. This uses a
// session-local span identity namespace, separate from each body registry.
pub(super) fn root_span(tcx: TyCtxt<'_>) -> Value {
    span(&mut SpanIds::new(), tcx, rustc_span::DUMMY_SP)
}
