//! Exact TyAbiInterface::{ty_and_layout_field,ty_and_layout_for_variant}
//! in rustc_middle/ty/layout.rs. Preserve query layouts, not layout-equivalent
//! type guesses; coroutine tags and uninhabited variants need these layouts.
use super::*;
fn parent<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    cx: &ty::layout::LayoutCx<'tcx>,
    layout: rustc_abi::TyAndLayout<'tcx, ty::Ty<'tcx>>,
    variant: Option<usize>,
) -> Result<pool_type::ProjectionParent, String> {
    // `TyAndLayout::field` has a source-defined `str` special case that
    // returns `u8` even though `str`'s layout has zero ordinary fields. Keep
    // that exact query result available to the importer without inventing a
    // field count or enumerating a synthetic array.
    let query_count = if matches!(layout.ty.kind(), ty::Str) {
        1
    } else {
        layout.fields.count()
    };
    let fields = (0..query_count)
        .map(|index| {
            let field = layout.field(cx, index);
            Ok(pool_type::ProjectionField {
                index,
                ty: type_json(context, tcx, field.ty)?,
                layout: if index == 0 && matches!(layout.ty.kind(),ty::RawPtr(..)|ty::Ref(..)) {
                    pointer_data_layout_value_json(context,field)
                } else if matches!(&layout.variants,rustc_abi::Variants::Multiple { tag_field,.. } if tag_field.index() == index) {
                    enum_tag_layout_value_json(context,layout)
                } else { layout_value_json(context,tcx,field) },
            })
        })
        .collect::<Result<_, String>>()?;
    Ok(pool_type::ProjectionParent {
        variant,
        layout: layout_value_json(context, tcx, layout),
        fields,
    })
}
pub(super) fn export<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    input: ty::Ty<'tcx>,
) -> Result<Option<pool_type::ProjectionQueries>, String> {
    if !matches!(
        input.kind(),
        ty::Closure(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::RawPtr(..)
            | ty::Ref(..)
            | ty::Adt(..)
            | ty::Pat(..)
            | ty::Str
    ) {
        return Ok(None);
    }
    if input.has_non_region_param()
        || input.has_escaping_bound_vars()
        || input.has_infer()
        || input.has_placeholders()
    {
        return export_failure(
            "projection queries",
            "projection queries require a complete monomorphic parent type",
        );
    }
    // These exact source constructors have fully ported field operations.
    // Non-erased regions retain their explicit query identity material.
    let covered = matches!(input.kind(),ty::Str)
        || matches!(*input.kind(),ty::RawPtr(pointee,_) | ty::Ref(_,pointee,_)
            if !input.has_free_regions() && pointer_recipe_eligible(tcx,pointee));
    if covered {
        layout_query_trace("projection-constructor",input,false);
        return Ok(None);
    }
    let env = ty::TypingEnv::fully_monomorphized();
    layout_query_trace("projection-parent",input,true);
    let layout = match tcx.layout_of(env.as_query_input(input)) {
        Ok(layout) => layout,
        Err(error) => {
            return Ok(export_failure(
                "projection_queries::export",
                format!(
                    "{}; {}",
                    "projection parent layout unavailable",
                    format!("{error:?}")
                ),
            )?);
        }
    };
    let cx = ty::layout::LayoutCx::new(tcx, env);
    let mut records = vec![parent(tcx, context, &cx, layout, None)?];
    let count = match input.kind() {
        ty::Adt(def, _) => def.variants().len(),
        ty::Coroutine(..) => match &layout.variants {
            rustc_abi::Variants::Multiple { variants, .. } => variants.len(),
            _ => 0,
        },
        _ => 0,
    };
    for index in 0..count {
        let selected = layout.for_variant(&cx, rustc_abi::VariantIdx::from_usize(index));
        records.push(parent(tcx, context, &cx, selected, Some(index))?);
    }
    Ok(Some(pool_type::ProjectionQueries {
        typing_env: "fully_monomorphized",
        parents: records,
    }))
}
