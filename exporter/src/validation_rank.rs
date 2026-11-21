//! Certificate for by-value descent. Pointer targets and generic arguments
//! are not children of the value that stores them.
use crate::pool_type::{Shape, Type};

pub(super) fn assign(types: &mut [Type]) -> Result<(), String> {
    let mut parents = vec![Vec::new(); types.len()];
    let mut pending = vec![0usize; types.len()];
    for (parent, node) in types.iter().enumerate() {
        let mut register = |child: u64| -> Result<(), String> {
            let rows = parents.get_mut(child as usize).ok_or_else(|| {
                format!("validation child {child} outside type pool for {parent}")
            })?;
            rows.push(parent);
            pending[parent] += 1;
            Ok(())
        };
        if node.source_layout.normalized_type != node.type_id {
            register(node.source_layout.normalized_type)?;
            continue;
        }
        match &node.shape {
            Shape::Adt { variants, .. } => {
                for field in variants.iter().flat_map(|variant| &variant.fields) {
                    register(field.ty)?;
                }
            }
            Shape::Array { element, .. } | Shape::Slice { element } => register(*element)?,
            Shape::PatternType { base, .. } => register(*base)?,
            Shape::UnsafeBinder { inner, .. } => register(*inner)?,
            Shape::Tuple { elements } => {
                for &child in elements {
                    register(child)?;
                }
            }
            Shape::Closure { .. } | Shape::CoroutineClosure { .. } => {
                for &child in &node.source_layout.closure_upvars {
                    register(child)?;
                }
            }
            Shape::Coroutine { .. } => {
                if let Some(layout) = &node.source_layout.coroutine {
                    for &child in &layout.prefix {
                        register(child)?;
                    }
                    for &field in layout.variants.iter().flatten() {
                        register(
                            *layout
                                .saved_types
                                .get(field)
                                .ok_or("missing coroutine saved type")?,
                        )?;
                    }
                }
            }
            _ => {}
        }
    }

    let mut ready: Vec<_> = (0..types.len()).filter(|&id| pending[id] == 0).collect();
    while let Some(child) = ready.pop() {
        let rank = types[child].validation_rank + 1;
        for &parent in &parents[child] {
            types[parent].validation_rank = types[parent].validation_rank.max(rank);
            pending[parent] -= 1;
            if pending[parent] == 0 {
                ready.push(parent);
            }
        }
    }
    if let Some(id) = pending.iter().position(|&count| count != 0) {
        return Err(format!("cyclic by-value layout dependency for type {id}"));
    }
    Ok(())
}
