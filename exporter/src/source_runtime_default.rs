//! Raw default-body syntax acquisition, never associated-item selection.
//! Capture every source-requested trait default declaration before Lean chooses
//! an impl/leaf. No Item instance, monomorphic MIR, ABI or selected target row is
//! produced. Unsupported source syntax stays an absent raw-template capability.
use rustc_middle::ty::{self,TyCtxt};
use super::{ExportContext,ctfe_body_source,generic_mir,pool_body,Value,
    span_json,def_json,mir_phase_json,source_info_json,backtrace_spans_json};
pub(super) fn capture<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,
    definition:rustc_hir::def_id::DefId)->Result<(),String> {
    if tcx.def_kind(definition)!=rustc_hir::def::DefKind::AssocFn {return Ok(())}
    let item=tcx.associated_item(definition);
    if !matches!(item.container,ty::AssocContainer::Trait) || !item.defaultness(tcx).has_value() {
        return Ok(())
    }
    let key=ctfe_body_source::TemplateKey {definition,promoted:None,role:ctfe_body_source::Role::Runtime};
    // Check source syntax before reserving; no incomplete pool entry is emitted.
    if !tcx.is_mir_available(definition) {return Ok(())}
    let template=tcx.optimized_mir(definition);
    let args=ty::GenericArgs::identity_for_item(tcx,definition);
    let Some(category)=generic_mir::source_category(tcx,template,args) else {return Ok(())};
    let (template_id,fresh)=context.mir_templates.reserve(key);
    if !fresh {return Ok(())}
            let raw = super::generic_mir::capture_category(tcx, template, category, |span|span_json(context,tcx,span))?;
            // Nominal types can occur only in a source local, without any
            // concrete caller type seeding their definitions. Capture their
            // declaration closure, never an instantiated type/body answer.
            let source_material:Value=serde_json::from_str(&raw)
                .map_err(|error|format!("source MIR material decoding failed: {error}"))?;
            let mut references=Vec::new();
            super::generic_definition_references(&source_material,&mut references)?;
            for definition in references { def_json(context,definition); }
            let source = pool_body::CopyTemplateSource {
                source_promoted:template.source.promoted.map(|index|index.as_u32()),
                source_role:ctfe_body_source::Role::Runtime.wire(),
                template: raw,
                source_def_id: def_json(context,template.source.def_id()),
                def_path: tcx.def_path_str(template.source.def_id()),
                span: span_json(context,tcx,template.span),
                preamble_def_span: span_json(context,tcx,tcx.def_span(template.source.def_id())),
                injection_phase: template.injection_phase.map(mir_phase_json),
                local_sources: template.local_decls.iter().map(|local|
                    source_info_json(context,tcx,local.source_info)).collect(),
                source_scopes: template.source_scopes.iter_enumerated().map(|(scope,value)|pool_body::SourceScope {
                    scope:scope.as_u32(),parent:value.parent_scope.map(|parent|parent.as_u32()),
                    span:span_json(context,tcx,value.span),inlined:None,
                    inlined_parent_scope:value.inlined_parent_scope.map(|parent|parent.as_u32()),
                }).collect(),
                backtrace_spans:backtrace_spans_json(context,tcx,template),
            };
            context.mir_templates.define(template_id,source);
    // Close raw default-to-default source dependencies without constructing a
    // selected target. The reserved template identity also bounds recursion.
    for block in template.basic_blocks.iter() {
        let rustc_middle::mir::TerminatorKind::Call {func,..} = &block.terminator().kind else {continue};
        let rustc_middle::mir::Operand::Constant(constant) = func else {continue};
        if let ty::FnDef(callee,_) = constant.const_.ty().kind() {
            capture(context,tcx,*callee)?;
        }
    }
    Ok(())
}
