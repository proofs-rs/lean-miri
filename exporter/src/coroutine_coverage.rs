//! Exact compiler-owned coroutine metadata; auxiliary bodies are never callable
//! instance bodies. Pinned StateTransform: coroutine/{mod,drop}.rs at 8144389c895d.
use super::*;
use crate::shared_json::Shared;

#[derive(serde::Serialize)]
pub(super) struct SavedField<T = u64> {
    pub r#type: T,
    pub source_info: Shared<pool_body::SourceInfo>,
    pub ignore_for_traits: bool,
    pub debuginfo_name: Option<String>,
}
#[derive(serde::Serialize)]
pub(super) struct Layout<T = u64> {
    pub field_tys: Vec<SavedField<T>>,
    pub variant_fields: Vec<Vec<usize>>,
    pub variant_source_info: Vec<pool_body::SourceInfo>,
    pub storage_conflicts: Vec<Vec<usize>>,
}
#[derive(serde::Serialize)]
pub(super) struct GenericSource {
    pub owner: serde_json::Value,
    pub physical_owner: serde_json::Value,
    pub typeck_owner: serde_json::Value,
    pub parent_count: usize,
    pub parameters: Vec<&'static str>,
    pub witness_parameters: Vec<&'static str>,
    pub type_expression: serde_json::Value,
    pub identity_kind: serde_json::Value,
    pub by_move_owner: Option<serde_json::Value>,
    pub layout: Layout<serde_json::Value>,
}
#[derive(serde::Serialize)]
pub(super) struct Coverage {
    pub owner_body: u64,
    pub coroutine_type: u64,
    pub coroutine_kind: pool_body::CoroutineKind,
    pub yield_type: Option<u64>,
    pub resume_type: Option<u64>,
    pub layout: Layout,
    pub drop_sync: Option<usize>,
    pub drop_async: Option<usize>,
    pub drop_proxy_async: Option<usize>,
}
#[derive(Clone, Copy, Debug, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum Role { Sync, Async, ProxyAsync }
#[derive(serde::Serialize)]
pub(super) struct Auxiliary<B = pool_body::Body> {
    pub owner_body: u64,
    pub role: Role,
    // source.instance can be the resume Item for async/proxy bodies. It must
    // never be used as an executable-body pool key (drop.rs:258,350).
    pub source_kind: pool_instance::InstanceKind,
    pub body: B,
}
#[derive(serde::Serialize)]
pub(super) struct Catalog<B = pool_body::Body> {
    pub generic_sources: Vec<GenericSource>,
    pub body_coroutines: Vec<bool>,
    pub coroutines: Vec<Coverage>,
    pub auxiliary_bodies: Vec<Auxiliary<B>>,
}
impl<B> Default for Catalog<B> {
    fn default() -> Self { Self { generic_sources: Vec::new(), body_coroutines: Vec::new(), coroutines: Vec::new(), auxiliary_bodies: Vec::new() } }
}
impl Catalog {
    pub fn finish(self, ids: &HashMap<(u64, Vec<u64>), u64>, candidates: &HashMap<u64, Vec<u64>>)
        -> Result<Catalog<pool_body::Body<u64, Vec<u64>>>, String> {
        Ok(Catalog { generic_sources: self.generic_sources, body_coroutines: self.body_coroutines, coroutines: self.coroutines, auxiliary_bodies: self.auxiliary_bodies.into_iter()
            .map(|row| Ok(Auxiliary { owner_body: row.owner_body, role: row.role,
                source_kind: row.source_kind, body: row.body.finish(ids, candidates)? }))
            .collect::<Result<_, String>>()? })
    }
}

// Capture raw declarations directly from physical optimized MIR. Query-selected
// layouts and closed field layout answers are intentionally not source inputs.
fn capture_generic_source<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>,
    owner: rustc_hir::def_id::DefId) -> Result<(), String> {
    if tcx.is_async_drop_in_place_coroutine(owner) { return Ok(()); }
    let ty::Coroutine(logical, args) = *tcx.type_of(owner).instantiate_identity().skip_norm_wip().kind()
        else { return Err("coroutine generic source: owner has no coroutine identity type".into()); };
    let identity = |def: rustc_hir::def_id::DefId| serde_json::json!({"crate":def.krate.as_u32(),"index":def.index.as_u32()});
    let owner_key = identity(logical);
    // Retain wrapper declarations for source-derived saved-local composition;
    // this registers no instantiated wrapper type and asks no layout query.
    if let Some(wrapper) = tcx.lang_items().maybe_uninit() { def_json(context,wrapper); }
    let by_move = tcx.needs_coroutine_by_move_body_def_id(logical)
        .then(|| tcx.coroutine_by_move_body_def_id(logical));
    let sorts = |def| (0..tcx.generics_of(def).count()).map(|index|
        match tcx.generics_of(def).param_at(index,tcx).kind {
            ty::GenericParamDefKind::Lifetime => "region",
            ty::GenericParamDefKind::Type {..} => "type",
            ty::GenericParamDefKind::Const {..} => "constant",
        }).collect::<Vec<_>>();
    let tree = |value| -> Result<serde_json::Value,String> {
        serde_json::from_str(&generic_material::type_tree(tcx,value)?).map_err(|error|error.to_string())
    };
    for physical in std::iter::once(logical).chain(by_move) {
        let physical_key = identity(physical);
        if context.coroutine_coverage.generic_sources.iter().any(|row|
            row.owner == owner_key && row.physical_owner == physical_key) { continue; }
        let body = tcx.optimized_mir(physical);
        let source = body.coroutine_layout_raw().ok_or("coroutine generic source: physical raw layout absent")?;
        let field_tys = source.field_tys.iter().map(|field| Ok(SavedField {
            r#type: tree(field.ty)?,
            source_info: source_info_json(context,tcx,field.source_info).into(),
            ignore_for_traits: field.ignore_for_traits,
            debuginfo_name: field.debuginfo_name.map(|name|name.to_string()),
        })).collect::<Result<Vec<_>,String>>()?;
        let layout = Layout {
            field_tys,
            variant_fields: source.variant_fields.iter().map(|row|row.iter().map(|field|field.index()).collect()).collect(),
            variant_source_info: source.variant_source_info.iter().map(|info|source_info_json(context,tcx,*info)).collect(),
            storage_conflicts: source.storage_conflicts.rows().map(|row|source.storage_conflicts.iter(row).map(|col|col.index()).collect()).collect(),
        };
        // Register declaration identities without inventing a callable body.
        def_json(context,logical); def_json(context,physical);
        let typeck = tcx.typeck_root_def_id(logical); def_json(context,typeck);
        let captured = GenericSource {
            owner:owner_key.clone(), physical_owner:physical_key, typeck_owner:identity(typeck),
            parent_count:tcx.generics_of(logical).parent_count,
            parameters:sorts(logical), witness_parameters:sorts(typeck),
            type_expression:tree(ty::Ty::new_coroutine(tcx,logical,args))?,
            identity_kind:tree(args.as_coroutine().kind_ty())?,
            by_move_owner:by_move.map(identity), layout,
        };
        let mut references = Vec::new();
        // Reference discovery traverses raw terms only. Source-info payloads
        // belong to the separate final shared_json::freeze pooling pass; they
        // are not type-definition reference discovery inputs.
        generic_definition_references(&captured.type_expression, &mut references)?;
        for field in &captured.layout.field_tys {
            generic_definition_references(&field.r#type, &mut references)?;
        }
        for reference in references { def_json(context,reference); }
        context.coroutine_coverage.generic_sources.push(captured);
    }
    Ok(())
}

fn lowered(body: &rustc_middle::mir::Body<'_>) -> Result<(), String> {
    use rustc_middle::mir::{MirPhase, TerminatorKind as T};
    if !matches!(body.phase, MirPhase::Runtime(_)) {
        return export_failure("coroutine coverage", "body has not reached runtime MIR");
    }
    for block in body.basic_blocks.iter() {
        if matches!(block.terminator().kind, T::Yield {..} | T::CoroutineDrop | T::FalseEdge {..} | T::FalseUnwind {..}) {
            return export_failure("coroutine coverage", "unlowered coroutine/control-flow terminator");
        }
    }
    Ok(())
}

pub(super) fn capture<'tcx>(tcx: TyCtxt<'tcx>, context: &mut ExportContext<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>, instance: ty::Instance<'tcx>, owner: u64) -> Result<(), String> {
    if context.coroutine_coverage.body_coroutines.len() <= owner as usize {
        context.coroutine_coverage.body_coroutines.resize(owner as usize + 1, false);
    }
    context.coroutine_coverage.body_coroutines[owner as usize] = body.coroutine.is_some();
    let Some(info) = body.coroutine.as_ref() else { return Ok(()) };
    lowered(body)?;
    if info.yield_ty.is_some() || info.resume_ty.is_some() {
        return export_failure("coroutine coverage", "unlowered yield/resume types");
    }
    let coroutine_ty = match body.source.instance {
        ty::InstanceKind::Item(def) => tcx.type_of(def).instantiate(tcx, instance.args).skip_norm_wip(),
        ty::InstanceKind::Shim(ty::ShimKind::AsyncDropGlue(_, value)) => value,
        _ => return export_failure("coroutine coverage", "unexpected coroutine body source kind"),
    };
    if !matches!(coroutine_ty.kind(), ty::Coroutine(..)) {
        return export_failure("coroutine coverage", "compiler body source is not a coroutine type");
    }
    if let ty::Coroutine(def, _) = *coroutine_ty.kind() { capture_generic_source(tcx,context,def)?; }
    let coroutine_type = type_json(context, tcx, coroutine_ty)?;
    let source = info.coroutine_layout.as_ref().ok_or("coroutine coverage: transformed layout is absent")?;
    let field_tys = source.field_tys.iter().map(|field| Ok(SavedField {
        // Source-template bodies retain raw saved-local types. Close only this
        // coverage oracle under the complete current instance, as state_tys
        // does; the genericSources declaration above remains untouched.
        r#type: type_json(context, tcx, tcx.erase_and_anonymize_regions(
            ty::EarlyBinder::bind(tcx,field.ty).instantiate(tcx,instance.args).skip_normalization()))?,
        source_info: source_info_json(context, tcx, field.source_info).into(),
        ignore_for_traits: field.ignore_for_traits,
        debuginfo_name: field.debuginfo_name.map(|name| name.to_string()),
    })).collect::<Result<Vec<_>, String>>()?;
    let variant_fields = source.variant_fields.iter().map(|fields|
        fields.iter().map(|field| field.index()).collect::<Vec<_>>()).collect::<Vec<_>>();
    let variant_source_info = source.variant_source_info.iter().map(|info|
        source_info_json(context, tcx, *info)).collect::<Vec<_>>();
    let storage_conflicts = source.storage_conflicts.rows().map(|row|
        source.storage_conflicts.iter(row).map(|column| column.index()).collect::<Vec<_>>()).collect::<Vec<_>>();
    if storage_conflicts.len() != field_tys.len() || variant_fields.len() != variant_source_info.len()
        || variant_fields.iter().chain(storage_conflicts.iter()).flatten().any(|index| *index >= field_tys.len()) {
        return export_failure("coroutine coverage", "compiler layout indices/dimensions disagree");
    }
    // Serialize all actual auxiliary MIR, not merely its presence. Canonical
    // DropGlue/FutureDropPoll remains separately supplied by instance_mir.
    let mut auxiliary = |value: &Option<rustc_middle::mir::Body<'tcx>>, role| -> Result<Option<usize>, String> {
        let Some(raw_value) = value else { return Ok(None) };
        // A selected source runtime template is deliberately uninstantiated.
        // Close its metadata-only auxiliary snapshot in the enclosing source
        // environment, exactly as the old whole-body normalization did. The
        // raw generic layout declaration and executable template stay raw.
        let closed_value = instance.try_instantiate_mir_and_normalize_erasing_regions(
            tcx, body.typing_env(tcx), ty::EarlyBinder::bind(tcx,raw_value.clone()),
        ).map_err(|error|format!("coroutine auxiliary snapshot instantiation failed: {error:?}"))?;
        let value = &closed_value;
        // Raw auxiliary snapshots are captured inside StateTransform, before
        // the pass manager advances Analysis(PostCleanup) to Runtime(Initial).
        // Sync drop explicitly advances its own phase (drop.rs:236–241).
        use rustc_middle::mir::{MirPhase as M, AnalysisPhase as A, RuntimePhase as R};
        let valid_phase = match role {
            Role::Sync => matches!(value.phase, M::Runtime(R::Initial)),
            Role::Async | Role::ProxyAsync => matches!(value.phase, M::Analysis(A::PostCleanup) | M::Runtime(R::Initial)),
        };
        if !valid_phase {
            return export_failure("coroutine coverage", "unexpected auxiliary snapshot phase");
        }
        // Check executable forms without pretending the metadata snapshot is
        // already the separately optimized canonical shim.
        for block in value.basic_blocks.iter() {
            use rustc_middle::mir::TerminatorKind as T;
            if matches!(block.terminator().kind, T::Yield {..} | T::CoroutineDrop | T::FalseEdge {..} | T::FalseUnwind {..}) {
                return export_failure("coroutine coverage", "unlowered auxiliary terminator");
            }
        }
        if value.coroutine.is_some() {
            return export_failure("coroutine coverage", "auxiliary drop body retains coroutine info");
        }
        let source_kind = instance_kind_json(context, tcx, value.source.instance)?;
        let definition = mir_body_json(tcx, value, instance, context, MirBodyRole::CoroutineAuxiliary).map_err(|error| {
            if error.contains("const_evaluation_error") {
                format!("{error}; coroutine_auxiliary role={role:?} owner={} source={} phase={:?}",
                    format!("{instance:?}").chars().take(1200).collect::<String>(),
                    format!("{:?}", value.source.instance).chars().take(1200).collect::<String>(), value.phase)
            } else { error }
        })?;
        let id = context.coroutine_coverage.auxiliary_bodies.len();
        context.coroutine_coverage.auxiliary_bodies.push(Auxiliary { owner_body: owner, role, source_kind, body: definition });
        Ok(Some(id))
    };
    let drop_sync = auxiliary(&info.coroutine_drop, Role::Sync)?;
    let drop_async = auxiliary(&info.coroutine_drop_async, Role::Async)?;
    let drop_proxy_async = auxiliary(&info.coroutine_drop_proxy_async, Role::ProxyAsync)?;
    if drop_sync.is_some() == drop_async.is_some() || drop_proxy_async.is_some() != drop_sync.is_some() {
        return export_failure("coroutine coverage", "compiler drop roles disagree");
    }
    context.coroutine_coverage.coroutines.push(Coverage { owner_body: owner, coroutine_type,
        coroutine_kind: coroutine_kind_json(info.coroutine_kind), yield_type: None, resume_type: None,
        layout: Layout { field_tys, variant_fields, variant_source_info, storage_conflicts },
        drop_sync, drop_async, drop_proxy_async });
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn body(instance: u64) -> pool_body::Body {
        pool_body::Body { source_role:"runtime", instance_id: instance, preamble_def_span: 0,
            backtrace_spans: Vec::new().into(), source_def_id: 7,
            phase: pool_body::Phase::Analysis { phase: pool_body::AnalysisPhase::PostCleanup },
            injection_phase: None, arg_count: 2, spread_arg: None, span: 0,
            locals: vec![], basic_blocks: vec![], source_scopes: vec![], required_consts: vec![] }
    }
    #[test]
    fn empty_catalog_is_explicit_and_role_tags_are_exact() {
        let catalog: Catalog<pool_body::Body<u64, Vec<u64>>> = Catalog::default();
        assert_eq!(serde_json::to_value(catalog).unwrap(), serde_json::json!({
            "generic_sources": [], "body_coroutines": [], "coroutines": [], "auxiliary_bodies": [] }));
        assert_eq!(serde_json::to_value(Role::Sync).unwrap(), "sync");
        assert_eq!(serde_json::to_value(Role::Async).unwrap(), "async");
        assert_eq!(serde_json::to_value(Role::ProxyAsync).unwrap(), "proxy_async");
    }
    #[test]
    fn auxiliary_roles_do_not_alias_when_source_instance_is_shared() {
        let catalog = Catalog { generic_sources: vec![], body_coroutines: vec![true], coroutines: vec![],
            auxiliary_bodies: vec![
                Auxiliary { owner_body: 0, role: Role::Async,
                    source_kind: pool_instance::InstanceKind::Item { def_id: 7 }, body: body(19) },
                Auxiliary { owner_body: 0, role: Role::ProxyAsync,
                    source_kind: pool_instance::InstanceKind::Item { def_id: 7 }, body: body(19) }] };
        let closed = catalog.finish(&HashMap::new(), &HashMap::new()).unwrap();
        let value = serde_json::to_value(closed).unwrap();
        let rows = value["auxiliary_bodies"].as_array().unwrap();
        assert_eq!(rows.len(), 2);
        assert_ne!(rows[0]["role"], rows[1]["role"]);
        assert_eq!(rows[0]["source_kind"], rows[1]["source_kind"]);
        for row in rows {
            assert_eq!(row["owner_body"], 0);
            assert_eq!(row["body"]["instance_id"], 19);
            assert_eq!(row["body"]["phase"]["kind"], "analysis");
        }
    }
}
