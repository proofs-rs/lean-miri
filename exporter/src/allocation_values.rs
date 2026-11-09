//! Semantic allocation graph data. Source allocation identity is independent of graph IDs.
use serde::Serialize;

#[derive(Clone, Serialize)]
pub(super) struct Memory {
    pub size_bytes: u64,
    pub align_bytes: u64,
    pub mutability: &'static str,
    pub bytes_hex: String,
    pub initialization_ranges: Vec<InitializationRange>,
    pub relocations: Vec<Relocation>,
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
}
