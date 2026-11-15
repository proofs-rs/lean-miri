//! Finite auto-trait declarations and complete manual-header exclusion material.
//! No obligation, selection, is_sync, is_freeze or vtable query is evaluated.
use super::*;

fn raw_definition(definition: DefId) -> Value {
    json!({"crate_index":definition.krate.as_u32(),"index":definition.index.as_u32()})
}
pub(super) fn outer_constructor(ty: ty::Ty<'_>) -> Value {
    // Rigid constructors cannot change under substitution. Alias/param/unknown
    // roots are deliberately not certified disjoint from a requested Self.
    match *ty.kind() {
        ty::Pat(base,pattern) => json!({"kind":"pattern","base":outer_constructor(base),
            "pattern_kind":if matches!(*pattern,ty::PatternKind::NotNull) {"not_null".to_string()} else {format!("{pattern:?}")}}),
        ty::Adt(def,_) => json!({"kind":"adt","definition":raw_definition(def.did())}),
        ty::FnDef(def,_) => json!({"kind":"fn_def","definition":raw_definition(def)}),
        ty::Closure(def,_) => json!({"kind":"closure","definition":raw_definition(def)}),
        ty::CoroutineClosure(def,_) => json!({"kind":"coroutine_closure","definition":raw_definition(def)}),
        ty::FnPtr(..) => json!({"kind":"fn_pointer"}),
        ty::Dynamic(..) => json!({"kind":"dynamic"}),
        ty::Tuple(elements) => json!({"kind":"tuple","arity":elements.len()}),
        ty::RawPtr(..) => json!({"kind":"raw_pointer"}),
        ty::Ref(..) => json!({"kind":"reference"}),
        ty::Array(..) => json!({"kind":"array"}),
        ty::Slice(..) => json!({"kind":"slice"}),
        ty::Str => json!({"kind":"str"}),
        ty::Bool => json!({"kind":"bool"}),ty::Char=>json!({"kind":"char"}),
        ty::Int(_)=>json!({"kind":"int"}),ty::Uint(_)=>json!({"kind":"uint"}),
        ty::Float(_)=>json!({"kind":"float"}),ty::Never=>json!({"kind":"never"}),
        _=>json!({"kind":"unknown"}),
    }
}
impl<'tcx> Material<'tcx> {
    pub(super) fn closure_auto_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let mut requested = Vec::new();
        for ty in self.type_ids.keys() {
            if let ty::Dynamic(predicates,_) = ty.kind() {
                for predicate in predicates.iter() {
                    if let ty::ExistentialPredicate::AutoTrait(definition) = predicate.skip_binder() {
                        requested.push(definition);
                    }
                }
            }
        }
        let unpin = tcx.lang_items().unpin_trait();
        let unsafe_unpin = tcx.lang_items().unsafe_unpin_trait();
        let freeze = tcx.lang_items().freeze_trait();
        if self.type_ids.keys().any(|ty| matches!(ty.kind(),ty::Closure(..)|ty::Dynamic(..))) {
            requested.extend([unpin,unsafe_unpin,freeze].into_iter().flatten());
        }
        requested.sort_by_key(|definition|(definition.krate.as_u32(),definition.index.as_u32()));
        requested.dedup();
        let mut declarations = Vec::new();
        for definition in requested {
            let generics = tcx.generics_of(definition);
            let clauses = tcx.explicit_clauses_of(definition);
            if generics.parent.is_some() || clauses.parent.is_some() {
                return unsupported("inherited closure auto trait declaration",definition);
            }
            let mut impls = tcx.all_impls(definition).collect::<Vec<_>>();
            impls.sort_by_key(|def|(def.krate.as_u32(),def.index.as_u32()));
            if impls.len() > 4096 {return unsupported("closure auto trait source header budget",impls.len());}
            let mut headers = Vec::new();
            for implementation in impls {
                let header = tcx.impl_trait_header(implementation);
                let reference = header.trait_ref.instantiate_identity().skip_normalization();
                let outer = outer_constructor(reference.self_ty());
                let mut record = json!({"definition":raw_definition(implementation),
                    "self_constructor":outer,"polarity":format!("{:?}",header.polarity)});
                if matches!(outer["kind"].as_str(),Some("unknown"|"closure"|"fn_pointer"|"tuple")) {
                    // A potential candidate cannot be discarded by outer type.
                    // Retain its source for diagnosis and require a future
                    // matcher: the current consumer always rejects this row.
                    let generics = tcx.generics_of(implementation);
                    record["potential_header"] = json!({
                        "trait_arguments":format!("{:?}",reference.args),
                        "parameters":format!("{generics:?}"),
                        "clauses":format!("{:?}",tcx.clauses_of(implementation)),
                        "constness":format!("{:?}",header.constness)});
                }
                headers.push(record);
            }
            let source_clauses = clauses.clauses.iter().map(|(clause,_)| {
                let bound = clause.kind();
                if bound.bound_vars().is_empty() {
                    if let ty::ClauseKind::Trait(predicate) = bound.skip_binder() {
                        if predicate.polarity == ty::ClausePolarity::Positive
                            && tcx.is_lang_item(predicate.trait_ref.def_id,rustc_attr_ir::LangItem::MetaSized)
                            && predicate.trait_ref.args.len() == 1
                            && matches!(predicate.trait_ref.self_ty().kind(),ty::Param(p) if p.index == 0) {
                            return json!({"kind":"meta_sized_self","definition":self.definition(tcx,predicate.trait_ref.def_id)});
                        }
                    }
                }
                json!({"kind":"unsupported","source":format!("{clause:?}")})
            }).collect::<Vec<_>>();
            let lang_item = if Some(definition) == unpin {Some("unpin")}
                else if Some(definition) == unsafe_unpin {Some("unsafe_unpin")}
                else if Some(definition) == freeze {Some("freeze")} else {None};
            declarations.push(json!({"definition":self.definition(tcx,definition),"lang_item":lang_item,
                "is_auto":tcx.trait_is_auto(definition),"safety":format!("{:?}",tcx.trait_def(definition).safety),
                "has_self":generics.has_self,"parameters":generics.own_params.iter().map(|p|match p.kind {
                    ty::GenericParamDefKind::Type {has_default,..} => json!({"index":p.index,"kind":"type","has_default":has_default}),
                    _ => json!({"index":p.index,"kind":"unsupported","source":format!("{:?}",p.kind)}),
                }).collect::<Vec<_>>(),
                "associated_item_count":tcx.associated_items(definition).in_definition_order().count(),
                "clauses":source_clauses,"complete_manual_headers":true,"manual_impl_headers":headers}));
        }
        Ok(json!({"declarations":declarations,"lang_items":{
            "unpin":unpin.map(|d|self.definition(tcx,d)),
            "unsafe_unpin":unsafe_unpin.map(|d|self.definition(tcx,d)),
            "freeze":freeze.map(|d|self.definition(tcx,d))}}))
    }
}
