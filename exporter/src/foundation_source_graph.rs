//! Finite definition discovery from uninstantiated MIR syntax. Only requested
//! roots and their executable operand/closure edges are traversed; structural
//! type references contribute headers only. The selected start is a declaration seed.
//! Calls contribute their source FnDef, never an implementation selection.
use super::*;
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable};
use std::collections::HashSet;

pub(super) struct Graph {
    pub selected: Vec<DefId>,
    pub call_declarations: Vec<DefId>,
    declarations: Vec<DefId>,
}
impl Graph {
    pub(super) fn declaration(&self, tcx: TyCtxt<'_>, path: &str) -> Result<DefId> {
        let mut matches = self.declarations.iter().copied()
            .filter(|definition| tcx.def_path_str(*definition) == path);
        let first = matches.next().ok_or_else(|| format!("foundation: missing source definition {path:?}"))?;
        if matches.next().is_some() { return unsupported("ambiguous source definition",path); }
        Ok(first)
    }
    pub(super) fn contains_body(&self, definition: DefId) -> bool {
        self.selected.contains(&definition)
    }
}

fn has_source_body(tcx: TyCtxt<'_>, definition: DefId) -> bool {
    matches!(tcx.def_kind(definition), rustc_hir::def::DefKind::Fn
        | rustc_hir::def::DefKind::AssocFn | rustc_hir::def::DefKind::Closure)
        && !super::super::is_required_trait_method(tcx,definition)
        && !tcx.is_foreign_item(definition)
        && !rustc_attr_ir::find_attr!(tcx,definition,RustcIntrinsic)
        && tcx.is_mir_available(definition)
}

fn syntax_edges(tcx: TyCtxt<'_>, owner: DefId) -> Result<(Vec<DefId>,Vec<DefId>,Vec<DefId>)> {
    if !tcx.is_mir_available(owner) { return unsupported("selected source MIR unavailable",owner); }
    let body = tcx.instance_mir(ty::InstanceKind::Item(owner));
    super::super::ensure_untainted_mir(body)?;
    if body.source.instance != ty::InstanceKind::Item(owner) || body.source.promoted.is_some()
        || body.coroutine.is_some() || !matches!(body.phase,mir::MirPhase::Runtime(_)) {
        return unsupported("source graph body identity",body.source);
    }
    // Visit only syntax already present in this body. Ty's structural visitor
    // follows generic arguments/signature children, not FnDef bodies/signatures
    // obtained through compiler queries or nominal declaration field layouts.
    struct FunctionTypes<'tcx> {
        seen: HashSet<ty::Ty<'tcx>>,
        definitions: Vec<DefId>,
    }
    impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for FunctionTypes<'tcx> {
        type Result = ();
        fn visit_ty(&mut self, value: ty::Ty<'tcx>) {
            if !self.seen.insert(value) { return; }
            if let ty::FnDef(definition,_) = *value.kind() { self.definitions.push(definition); }
            value.super_visit_with(self);
        }
    }
    struct BodyTypes<'a,'tcx> { functions: &'a mut FunctionTypes<'tcx>,
        bodies: &'a mut Vec<DefId>, tcx: TyCtxt<'tcx>, body: &'a mir::Body<'tcx> }
    impl<'tcx> mir::visit::Visitor<'tcx> for BodyTypes<'_,'tcx> {
        fn visit_ty(&mut self, value: ty::Ty<'tcx>, _: mir::visit::TyContext) {
            value.visit_with(self.functions);
        }
        fn visit_ty_const(&mut self, value: ty::Const<'tcx>, _: mir::Location) {
            value.visit_with(self.functions);
        }
        fn visit_operand(&mut self, value: &mir::Operand<'tcx>, location: mir::Location) {
            // A function value may execute through a pointer or a generic
            // callable parameter. Only its outer FnDef is an executable edge;
            // FnDefs nested in generic type arguments remain header demands.
            if let ty::FnDef(definition,_) = *value.ty(self.body,self.tcx).kind() {
                self.bodies.push(definition);
            }
            self.super_operand(value,location);
        }
    }
    let mut functions = FunctionTypes {seen:HashSet::new(),definitions:Vec::new()};
    let mut body_edges = Vec::new();
    mir::visit::Visitor::visit_body(&mut BodyTypes {functions:&mut functions,
        bodies:&mut body_edges,tcx,body},body);
    let mut result = functions.definitions.clone();
    let mut calls = functions.definitions;
    for block in body.basic_blocks.iter() {
        if let mir::TerminatorKind::Call {func,..} = &block.terminator().kind {
            if let ty::FnDef(definition,_) = *func.ty(body,tcx).kind() {
                result.push(definition); calls.push(definition);
            }
        }
        for statement in &block.statements {
            if let mir::StatementKind::Assign(assignment) = &statement.kind {
                if let mir::Rvalue::Aggregate(kind,_) = &assignment.1 {
                    if let mir::AggregateKind::Closure(definition,_) = **kind {
                        result.push(definition); body_edges.push(definition);
                    }
                }
            }
        }
    }
    // Executable edges must also remain declaration identities, independently
    // of whether the structural type visitor visits that operand type again.
    result.extend(body_edges.iter().copied());
    result.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    result.dedup();
    calls.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    calls.dedup();
    body_edges.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    body_edges.dedup();
    Ok((result,calls,body_edges))
}

pub(super) fn discover(tcx: TyCtxt<'_>, roots: &[String], signatures: &[String]) -> Result<Graph> {
    let items = tcx.hir_crate_items(());
    let mut declarations = items.definitions().chain(items.nested_bodies()).map(|d|d.to_def_id())
        .collect::<Vec<_>>();
    declarations.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    declarations.dedup();
    let mut selected = declarations.iter().copied().filter(|definition| {
        has_source_body(tcx,*definition)
            && (roots.is_empty() || roots.contains(&tcx.def_path_str(*definition)))
    }).collect::<Vec<_>>();
    let mut pending = selected.clone();
    // This is language-item semantics, independent of std names. A signature-
    // only demand may inspect this compiler-selected source owner without
    // claiming that its executable body has been supplied.
    if let Some(start) = tcx.lang_items().start_fn() {
        if !declarations.contains(&start) { declarations.push(start); }
        if roots.contains(&tcx.def_path_str(start)) {
            if !selected.contains(&start) { selected.push(start); pending.push(start); }
        } else if roots.iter().chain(signatures).any(|name| !declarations.iter().any(|d|tcx.def_path_str(*d)==*name)) {
            pending.push(start);
        }
    }
    let mut visited = HashSet::new();
    let mut call_declarations = Vec::new();
    while let Some(owner) = pending.pop() {
        if !visited.insert(owner) { continue; }
        let (edges,calls,body_edges) = syntax_edges(tcx,owner)?;
        if selected.contains(&owner) { call_declarations.extend(calls); }
        for definition in edges {
            if !declarations.contains(&definition) { declarations.push(definition); }
            let explicit = roots.contains(&tcx.def_path_str(definition));
            let executable = selected.contains(&owner) && body_edges.contains(&definition);
            if (explicit || executable) && has_source_body(tcx,definition) && !selected.contains(&definition) {
                selected.push(definition);
                pending.push(definition);
            }
        }
    }
    selected.sort_by_key(|definition|tcx.def_path_str(*definition));
    selected.dedup();
    for root in roots {
        if !selected.iter().any(|definition|tcx.def_path_str(*definition)==*root) {
            return Err(format!("foundation: missing MIR root {root:?}"));
        }
    }
    call_declarations.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
    call_declarations.dedup();
    Ok(Graph {selected,declarations,call_declarations})
}
