//! Complete finite source headers for local, ordinary methodless traits.
//! No goals, substitutions, selection results or candidate answers are exported.
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{json, Value};

type Result<T> = std::result::Result<T, String>;
fn reject<T>(what: &str, def: DefId) -> Result<T> {
    Err(format!("foundation: unsupported local trait {what}: {def:?}"))
}
fn meta_sized_clause<'tcx>(tcx: TyCtxt<'tcx>, clause: ty::Clause<'tcx>, owner: DefId) -> Result<Value> {
    let bound = clause.kind();
    if !bound.bound_vars().is_empty() { return reject("bound super clauses", owner); }
    if let ty::ClauseKind::Trait(predicate) = bound.skip_binder() {
        if predicate.polarity == ty::ClausePolarity::Positive
            && tcx.is_lang_item(predicate.trait_ref.def_id,rustc_attr_ir::LangItem::MetaSized)
            && predicate.trait_ref.args.len() == 1
            && matches!(predicate.trait_ref.self_ty().kind(),ty::Param(p) if p.index == 0) {
            let def = predicate.trait_ref.def_id;
            return Ok(json!({"kind":"self_trait","lang_item":"meta_sized",
                "crate_index":def.krate.as_u32(),"index":def.index.as_u32(),
                "path":tcx.def_path_str(def),"self_parameter":0}));
        }
    }
    reject("super clauses", owner)
}
fn parameter_clause<'tcx>(tcx: TyCtxt<'tcx>, clause: ty::Clause<'tcx>, owner: DefId) -> Result<Value> {
    let bound = clause.kind();
    if !bound.bound_vars().is_empty() { return reject("bound impl clauses", owner); }
    if let ty::ClauseKind::Trait(predicate) = bound.skip_binder() {
        let def = predicate.trait_ref.def_id;
        let lang_item = if tcx.is_lang_item(def,rustc_attr_ir::LangItem::Sized) { "sized" }
            else if tcx.is_lang_item(def,rustc_attr_ir::LangItem::Copy) { "copy" }
            else if tcx.is_lang_item(def,rustc_attr_ir::LangItem::MetaSized) { "meta_sized" }
            else { return reject("conditional impl clause", owner); };
        // Copy's structural leaf rules below follow pinned core::marker, not
        // an arbitrary user-provided no_core language trait. Producer artifact
        // hashes retain the existing independently-pinned sysroot requirement.
        if lang_item == "copy" && (def.is_local() || tcx.crate_name(def.krate).as_str() != "core"
            || rustc_attr_ir::find_attr!(tcx, crate, NoCore)) {
            return reject("non-core Copy implementation source", owner);
        }
        if predicate.polarity == ty::ClausePolarity::Positive
            && predicate.trait_ref.args.len() == 1
            && matches!(predicate.trait_ref.self_ty().kind(),ty::Param(p) if p.index == 0) {
            return Ok(json!({"kind":"parameter_trait","lang_item":lang_item,
                "crate_index":def.krate.as_u32(),"index":def.index.as_u32(),
                "path":tcx.def_path_str(def),"parameter":0,
                "implementation_source":if lang_item == "copy" {"pinned_core_marker"} else {"compiler_builtin"}}));
        }
    }
    reject("conditional impl clause", owner)
}
pub(super) fn capture(tcx: TyCtxt<'_>, def: DefId) -> Result<Value> {
    if !def.is_local() { return reject("external identity", def); }
    let generics = tcx.generics_of(def);
    if generics.parent.is_some() || generics.count() != 1 || !generics.has_self {
        return reject("generic parameters", def);
    }
    let declaration = tcx.trait_def(def);
    if tcx.trait_is_auto(def) || declaration.is_marker || declaration.is_coinductive {
        return reject("auto/overlapping/coinductive declaration", def);
    }
    if !matches!(declaration.constness, rustc_hir::Constness::NotConst) {
        return reject("const declaration", def);
    }
    if declaration.safety != rustc_hir::Safety::Safe {
        return reject("unsafe declaration", def);
    }
    if tcx.associated_items(def).in_definition_order().next().is_some() {
        return reject("associated items", def);
    }
    // Pinned hir_ty_lowering/bounds.rs adds MetaSized to ordinary traits.
    // Preserve its exact language-item identity; every supported impl Self is
    // a primitive or fixed array and hence has fixed, thin metadata. Other
    // supertrait clauses reject; impl parameter clauses are retained below.
    let super_clauses = tcx.explicit_super_clauses_of(def).skip_binder().iter()
        .map(|(clause,_)| meta_sized_clause(tcx,*clause,def)).collect::<Result<Vec<_>>>()?;
    let clauses = tcx.explicit_clauses_of(def);
    if clauses.parent.is_some() { return reject("inherited declaration clauses", def); }
    for (clause,_) in clauses.clauses {
        meta_sized_clause(tcx,*clause,def)?;
    }
    // Pinned ty/trait_def.rs::all_impls enumerates blanket and non-blanket
    // source headers. Its provider explicitly notes a local trait cannot have
    // impls in upstream crates. Therefore this table is complete for this crate,
    // independent of which concrete obligation a consumer will later demand.
    let mut impls = tcx.all_impls(def).collect::<Vec<_>>();
    impls.sort_by_key(|d|tcx.def_path_str(*d));
    let implementations = impls.into_iter().map(|implementation| {
        let generics = tcx.generics_of(implementation);
        let clauses = tcx.clauses_of(implementation);
        if !implementation.is_local() || generics.parent.is_some() || clauses.parent.is_some() {
            return reject("inherited impl environment", implementation);
        }
        let generic_array = generics.count() == 1 && generics.own_params.iter().all(|p|
            p.index == 0 && matches!(p.kind,ty::GenericParamDefKind::Type {has_default:false,..}));
        if generics.count() != 0 && !generic_array {
            return reject("generic or conditional impl", implementation);
        }
        let parameters = if generic_array { vec![json!({"kind":"type","index":0})] } else { vec![] };
        let impl_clauses = if generic_array {
            clauses.clauses.iter().map(|(clause,_)|parameter_clause(tcx,*clause,implementation))
                .collect::<Result<Vec<_>>>()?
        } else {
            if !clauses.clauses.is_empty() { return reject("conditional primitive impl", implementation); }
            vec![]
        };
        let header = tcx.impl_trait_header(implementation);
        if !matches!(header.constness, rustc_hir::Constness::NotConst) {
            return reject("const impl", implementation);
        }
        if header.polarity != ty::ImplPolarity::Positive {
            return reject("negative impl", implementation);
        }
        let reference = header.trait_ref.instantiate_identity().skip_normalization();
        if reference.def_id != def || reference.args.len() != 1 {
            return reject("impl arguments", implementation);
        }
        let self_type = if generic_array {
            // A canonical one-parameter array blanket header. The literal const
            // is already finite TypeIR material: no const-eval/selection query.
            let ty::Array(element,length) = *reference.self_ty().kind()
                else { return reject("generic or conditional impl self pattern", implementation); };
            if !matches!(element.kind(),ty::Param(p) if p.index == 0) {
                return reject("generic array element pattern", implementation);
            }
            let ty::ConstKind::Value(length) = length.kind()
                else { return reject("generic array length pattern", implementation); };
            if length.ty != tcx.types.usize { return reject("array length type", implementation); }
            let Some(leaf) = length.valtree.try_to_leaf()
                else { return reject("array length constant", implementation); };
            json!({"kind":"array_pattern","element_parameter":0,
                "length":leaf.to_bits(leaf.size()).to_string()})
        } else { match *reference.self_ty().kind() {
            ty::Bool => json!({"kind":"bool","name":""}),
            ty::Char => json!({"kind":"char","name":""}),
            ty::Int(i) => json!({"kind":"int","name":i.name_str()}),
            ty::Uint(i) => json!({"kind":"uint","name":i.name_str()}),
            ty::Float(i) => json!({"kind":"float","name":i.name_str()}),
            _ => return reject("non-primitive impl self type", implementation),
        }};
        Ok(json!({"crate_index":implementation.krate.as_u32(),
            "index":implementation.index.as_u32(),"path":tcx.def_path_str(implementation),
            "polarity":"positive","parameters":parameters,"clauses":impl_clauses,"self_type":self_type}))
    }).collect::<Result<Vec<_>>>()?;
    Ok(json!({"source_kind":"local_ordinary_methodless_trait",
        "complete_impl_headers":true,"parameters":[{"kind":"self","index":0}],
        "super_clauses":super_clauses,"associated_items":[],"implementations":implementations}))
}
