//! Semantic allocation graph data. Source allocation identity is independent of graph IDs.
use serde::Serialize;
use crate::shared_json::Shared;

#[derive(Clone, Serialize)]
pub(super) struct Memory {
    pub size_bytes: u64,
    pub align_bytes: u64,
    pub mutability: &'static str,
    pub byte_image_id: u64,
    pub initialization_ranges: Shared<Vec<InitializationRange>>,
    pub relocations: Shared<Vec<Relocation>>,
}
#[derive(Clone, Serialize)]
pub(super) struct InitializationRange {
    pub state: &'static str,
    pub start_bytes: u64,
    pub end_bytes_exclusive: u64,
}
#[derive(Clone, Serialize)]
pub(super) struct Relocation {
    pub storage_offset_bytes: u64,
    pub target: u64,
    pub target_offset_encoded_bytes: String,
    pub immutable: bool,
    pub shared_ref: bool,
}
#[derive(Clone, Serialize)]
pub(super) struct StaticGlobalInfo {
    pub size_bytes: u64,
    pub align_bytes: u64,
    pub mutability: &'static str,
    pub is_static: bool,
    pub is_foreign_item: bool,
    pub nested: bool,
    pub thread_local: bool,
}

#[derive(Clone, Serialize)]
pub(super) struct Allocation {
    pub allocation_id: u64,
    pub source_alloc_id: u64,
    #[serde(flatten)]
    pub data: AllocationData,
}
impl Allocation {
    pub fn memory(&self) -> Option<&Memory> {
        match &self.data {
            AllocationData::Memory { memory } => Some(memory),
            _ => None,
        }
    }

    pub fn kind(&self) -> &'static str {
        match self.data {
            AllocationData::Memory { .. } => "memory",
            AllocationData::Function { .. } => "function",
            AllocationData::Static { .. } => "static",
            AllocationData::Vtable { .. } => "vtable",
            AllocationData::TypeId { .. } => "type_id",
        }
    }
}
#[derive(Serialize)]
#[serde(untagged)]
pub(super) enum Entry {
    Single(Allocation),
    Functions {
        // Grouping must preserve both pointer identity and the compiler reservation history.
        kind: &'static str,
        instance_id: u64,
        identities: Vec<[u64; 2]>,
    },
}

pub(super) fn compact(nodes: Vec<Allocation>) -> Vec<Entry> {
    let mut entries = Vec::new();
    let mut functions = std::collections::HashMap::new();
    for node in nodes {
        if let AllocationData::Function { instance_id } = node.data {
            let identity = [node.allocation_id, node.source_alloc_id];
            let index = *functions.entry(instance_id).or_insert_with(|| {
                let index = entries.len();
                entries.push(Entry::Functions {
                    kind: "function",
                    instance_id,
                    identities: Vec::new(),
                });
                index
            });
            let Entry::Functions { identities, .. } = &mut entries[index] else {
                unreachable!()
            };
            identities.push(identity);
        } else {
            entries.push(Entry::Single(node));
        }
    }
    entries
}

#[derive(Default)]
pub(super) struct ByteImages {
    // Equal bytes may share storage while their allocations retain independent identities.
    ids: std::collections::HashMap<Vec<u8>, u64>,
    images: Vec<String>,
}
impl ByteImages {
    pub(super) fn intern(&mut self, bytes: &[u8]) -> u64 {
        if let Some(&id) = self.ids.get(bytes) {
            return id;
        }
        let id = self.images.len() as u64;
        self.ids.insert(bytes.to_vec(), id);
        self.images.push(super::bytes_hex(bytes));
        id
    }

    pub(super) fn finish(self) -> Vec<String> {
        self.images
    }
}

#[derive(Clone, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum AllocationData {
    Memory {
        #[serde(flatten)]
        memory: Memory,
    },
    Function {
        instance_id: u64,
    },
    Static {
        def_id: u64,
        def_path: String,
        thread_local: bool,
        global_info: StaticGlobalInfo,
        #[serde(skip_serializing_if = "Option::is_none")]
        initializer: Option<Memory>,
    },
    Vtable {
        #[serde(rename = "type")]
        ty: u64,
        size_bytes: u64,
        align_bytes: u64,
        predicates: Vec<u64>,
        principal_predicate: Option<u64>,
        entries: Vec<VtableEntry>,
    },
    TypeId {
        #[serde(rename = "type")]
        ty: u64,
    },
}
#[derive(Clone, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum VtableEntry {
    DropInPlace {
        instance_id: u64,
    },
    DropInPlaceNull,
    SizeBytes,
    AlignBytes,
    Vacant,
    Method {
        instance_id: u64,
    },
    SupertraitVtablePointer {
        trait_def_id: u64,
        trait_def_path: String,
        generic_args: Vec<super::pool_values::GenericArgument>,
        allocation: u64,
    },
}

#[derive(Clone, Serialize)]
pub(super) struct Predicate {
    #[serde(flatten)]
    pub data: PredicateData,
    pub bound_variables: Vec<super::pool_values::BoundVariable>,
}
#[derive(Clone, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum PredicateData {
    Trait {
        def_id: u64,
        def_path: String,
        generic_args: Vec<super::pool_values::GenericArgument>,
    },
    AutoTrait {
        def_id: u64,
        def_path: String,
    },
    Projection {
        def_id: u64,
        def_path: String,
        generic_args: Vec<super::pool_values::GenericArgument>,
        term: ProjectionTerm,
    },
}
#[derive(Clone, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub(super) enum ProjectionTerm {
    Type(u64),
    Const(u64),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function(graph: u64, source: u64, instance_id: u64) -> Allocation {
        Allocation {
            allocation_id: graph,
            source_alloc_id: source,
            data: AllocationData::Function { instance_id },
        }
    }

    #[test]
    fn grouping_keeps_each_graph_and_noncontiguous_source_identity() {
        let entries = compact(vec![
            function(0, 91, 3),
            function(1, 8, 7),
            Allocation {
                allocation_id: 2,
                source_alloc_id: 24,
                data: AllocationData::TypeId { ty: 6 },
            },
            function(3, 105, 3),
            function(4, 2, 7),
        ]);
        assert_eq!(
            serde_json::to_string(&entries).unwrap(),
            r#"[{"kind":"function","instance_id":3,"identities":[[0,91],[3,105]]},{"kind":"function","instance_id":7,"identities":[[1,8],[4,2]]},{"allocation_id":2,"source_alloc_id":24,"kind":"type_id","type":6}]"#
        );
    }

    #[test]
    fn exact_images_share_bytes_without_merging_allocations() {
        let mut images = ByteImages::default();
        let first = images.intern(&[0, 1, 255]);
        let second = images.intern(&[0, 1, 255]);
        assert_eq!(first, second);
        assert_ne!(first, images.intern(&[0, 1]));
        assert_ne!(first, images.intern(&[0, 1, 254]));
        let empty = images.intern(&[]);
        assert_eq!(empty, images.intern(&[]));
        let memory = |graph, source, byte_image_id| Allocation {
            allocation_id: graph,
            source_alloc_id: source,
            data: AllocationData::Memory {
                memory: Memory {
                    size_bytes: 3,
                    align_bytes: 1,
                    mutability: "immutable",
                    byte_image_id,
                    initialization_ranges: vec![InitializationRange {
                        state: "initialized",
                        start_bytes: 0,
                        end_bytes_exclusive: 3,
                    }].into(),
                    relocations: Vec::new().into(),
                },
            },
        };
        let entries = compact(vec![memory(0, 17, first), memory(1, 48, second)]);
        assert!(matches!(&entries[..], [Entry::Single(a), Entry::Single(b)]
            if a.allocation_id != b.allocation_id && a.source_alloc_id != b.source_alloc_id));
        assert_eq!(images.finish(), ["0001ff", "0001", "0001fe", ""]);
    }
}
