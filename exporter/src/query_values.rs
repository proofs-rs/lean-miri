//! Typed compiler query catalogs and their local reference finalization.
use serde::Serialize;
use std::collections::HashMap;
#[derive(Clone, Serialize)]
pub(super) struct PredicateQuery {
    pub predicate_id: usize,
    pub typing_env: &'static str,
    pub auto_trait: bool,
    pub original: u64,
    pub normalization: u64,
    pub stable_key: u64,
}
#[derive(Clone, Serialize)]
pub(super) struct RuntimeTypeQuery {
    pub input_type_id: u64,
    pub typing_env: &'static str,
    pub mut_pointer_type: u64,
    pub mut_reference_type: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub drop_glue: Option<u64>,
}
#[derive(Clone)]
pub(super) struct PendingVtableRef {
    pub input_type: u64,
    pub input_predicates: Vec<u64>,
    pub key: (u64, Vec<u64>),
}
#[derive(Clone, Serialize)]
pub(super) struct VtableRef {
    pub input_type: u64,
    pub input_predicates: Vec<u64>,
    pub query_id: u64,
}
impl PendingVtableRef {
    pub fn finish(self, ids: &HashMap<(u64, Vec<u64>), u64>) -> Result<VtableRef, String> {
        let query_id = *ids
            .get(&self.key)
            .ok_or("vtable query is absent from the finalized compiler catalog")?;
        Ok(VtableRef {
            input_type: self.input_type,
            input_predicates: self.input_predicates,
            query_id,
        })
    }
}
#[derive(Clone, Serialize)]
pub(super) struct RuntimeVirtualQuery<R> {
    pub typing_env: &'static str,
    pub original_instance_id: u64,
    pub method_definition: u64,
    pub parent_trait: u64,
    pub concrete_type: u64,
    pub rebased_args: Vec<super::pool_values::GenericArgument>,
    pub resolved: u64,
    pub vtable_query: R,
}
#[derive(Clone, Serialize)]
pub(super) struct VtableMetadata {
    pub r#type: u64,
    pub size_bytes: Option<u64>,
    pub align_bytes: Option<u64>,
    pub predicates: Vec<u64>,
    pub principal_predicate: Option<u64>,
    pub entries: Vec<super::allocation_values::VtableEntry>,
}
#[derive(Clone, Serialize)]
pub(super) struct VtableQuery {
    pub query_id: u64,
    pub input_type: u64,
    pub input_predicates: Vec<u64>,
    pub output_type: u64,
    pub output_predicates: Vec<u64>,
    pub output_type_monomorphic_enough: bool,
    pub output_predicates_monomorphic_enough: bool,
    pub vtable_allocation_id: Option<u64>,
    pub vtable_metadata: VtableMetadata,
}

/// Index only exact virtual-instance query rows, preserving sorted unique IDs.
pub(super) fn virtual_candidates(
    rows: &[RuntimeVirtualQuery<VtableRef>],
) -> HashMap<u64, Vec<u64>> {
    let mut candidates = HashMap::<u64, Vec<u64>>::new();
    for row in rows {
        candidates
            .entry(row.original_instance_id)
            .or_default()
            .push(row.vtable_query.query_id);
    }
    for ids in candidates.values_mut() {
        ids.sort_unstable();
        ids.dedup();
    }
    candidates
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finalization_requires_the_exact_predicate_vector() {
        let ids = HashMap::from([((3, vec![5, 7]), 11)]);
        let missing = PendingVtableRef {
            input_type: 3,
            input_predicates: vec![7, 5],
            key: (3, vec![7, 5]),
        };
        assert!(missing.finish(&ids).is_err());
        let found = PendingVtableRef {
            input_type: 3,
            input_predicates: vec![5, 7],
            key: (3, vec![5, 7]),
        }
        .finish(&ids)
        .unwrap();
        assert_eq!(
            serde_json::to_value(found).unwrap(),
            serde_json::json!({"input_type":3,"input_predicates":[5,7],"query_id":11})
        );
    }
    #[test]
    fn virtual_candidates_sort_deduplicate_and_keep_instances_separate() {
        let row = |instance, query| RuntimeVirtualQuery {
            typing_env: "fully_monomorphized",
            original_instance_id: instance,
            method_definition: 1,
            parent_trait: 2,
            concrete_type: 3,
            rebased_args: Vec::new(),
            resolved: 4,
            vtable_query: VtableRef {
                input_type: 3,
                input_predicates: vec![],
                query_id: query,
            },
        };
        let candidates = virtual_candidates(&[row(10, 7), row(20, 3), row(10, 2), row(10, 7)]);
        assert_eq!(candidates.get(&10), Some(&vec![2, 7]));
        assert_eq!(candidates.get(&20), Some(&vec![3]));
        assert!(!candidates.contains_key(&30));
    }
}
