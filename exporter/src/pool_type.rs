//! Semantic type graph stored while collecting compiler facts.
use crate::pool_values::{BoundVariable, GenericArgument, Region};
use serde::Serialize;
use crate::shared_json::Shared;
#[derive(Clone, Debug, Serialize)]
pub(super) struct Type {
    pub type_id: u64,
    pub display: String,
    pub shape: Shape,
    pub layout: u64,
    pub layout_query_input_type: Option<u64>,
    pub compiler_facts: CompilerFacts,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Shape {
    Bool,
    Char,
    Int {
        signed_kind: &'static str,
    },
    Uint {
        unsigned_kind: &'static str,
    },
    Float {
        float_kind: &'static str,
    },
    Adt {
        def_id: u64,
        def_path: String,
        adt_kind: &'static str,
        representation: Representation,
        generic_args: Vec<GenericArgument>,
        variants: Vec<Variant>,
    },
    Foreign {
        def_id: u64,
        def_path: String,
    },
    Str,
    Array {
        element: u64,
        length: u64,
        constructor_identity: ArrayIdentity,
    },
    PatternType {
        base: u64,
        pattern: Pattern,
    },
    Slice {
        element: u64,
    },
    RawPointer {
        mutability: Mutability,
        pointee: u64,
    },
    Reference {
        region: Region,
        mutability: Mutability,
        pointee: u64,
    },
    FunctionDefinition {
        def_id: u64,
        def_path: String,
        generic_args: Vec<GenericArgument>,
        generic_args_bound_variables: Vec<BoundVariable>,
        signature: FunctionSignature,
        signature_bound_variables: Vec<BoundVariable>,
    },
    FunctionPointer {
        signature: FunctionSignature,
        signature_bound_variables: Vec<BoundVariable>,
    },
    UnsafeBinder {
        inner: u64,
        bound_variables: Vec<BoundVariable>,
    },
    DynamicTraitObject {
        region: Region,
        predicates: Vec<u64>,
        principal_predicate: Option<u64>,
    },
    Closure {
        def_id: u64,
        def_path: String,
        generic_args: Vec<GenericArgument>,
        upvar_count: usize,
    },
    CoroutineClosure {
        def_id: u64,
        def_path: String,
        generic_args: Vec<GenericArgument>,
    },
    Coroutine {
        def_id: u64,
        def_path: String,
        generic_args: Vec<GenericArgument>,
    },
    Never,
    Tuple {
        elements: Vec<u64>,
    },
    Alias {
        rigid: bool,
        alias_payload: Alias,
        def_id: u64,
        generic_args: Vec<GenericArgument>,
    },
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Variant {
    pub index: u32,
    pub name: String,
    pub fields: Vec<Field>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Field {
    pub index: u32,
    pub name: String,
    #[serde(rename = "type")]
    pub ty: u64,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct ArrayIdentity {
    pub count: u64,
    pub canonical_value_constructor: bool,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Pattern {
    Range { start: u64, end: u64 },
    Or { patterns: Vec<Pattern> },
    NotNull,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Mutability {
    Mutable,
    Immutable,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Safety {
    Safe,
    Unsafe,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct ExternAbi {
    pub kind: &'static str,
    pub unwind: Option<bool>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct FunctionSignature {
    pub inputs: Vec<u64>,
    pub output: u64,
    pub safety: Safety,
    pub abi: ExternAbi,
    pub c_variadic: bool,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Alias {
    pub kind: &'static str,
    pub def_id: u64,
    pub def_path: String,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Representation {
    pub integer: Option<RepresentationInteger>,
    pub align_bytes: Option<u64>,
    pub pack_bytes: Option<u64>,
    pub flags_bits: u8,
    pub scalable_element: Option<ScalableElement>,
    pub field_shuffle_seed: u64,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum RepresentationInteger {
    PointerSized {
        signed: bool,
    },
    Fixed {
        integer_kind: &'static str,
        size_bits: u64,
        signed: bool,
    },
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum ScalableElement {
    ElementCount { count: u64 },
    Container,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct CompilerFacts {
    pub typing_env: &'static str,
    pub boolean_queries: Shared<BooleanQueries>,
    pub type_queries: TypeQueries,
    pub adt: Option<AdtFacts>,
    pub capture_names: Option<Vec<Option<String>>>,
    pub simd_size_and_type: Option<Simd>,
    pub discriminants: Shared<Discriminants>,
    pub projection_queries: Option<ProjectionQueries>,
    pub definition: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub type_id_hash: Option<String>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct BooleanQueries {
    pub is_unsafe_cell: bool,
    pub has_erasable_regions: bool,
    pub is_c_void: bool,
    pub is_simd: bool,
    pub is_box: bool,
    pub is_global_box: bool,
    pub is_monomorphic: bool,
    pub is_monomorphic_enough: bool,
    pub is_like_maybe_dangling: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_freeze: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_unpin: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_unsafe_unpin: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub needs_drop: Option<bool>,
    pub opsem_inhabited: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub is_sized: Option<bool>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct TypeQueries {
    pub discriminant_type: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized: Option<u64>,
    pub unsafe_binder_erased: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub pointer_metadata_type: Option<u64>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct AdtFacts {
    pub definition: u64,
    pub item_name: String,
    pub nonnull_optimization_guaranteed: bool,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Simd {
    pub count: u64,
    pub element: u64,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Discriminants {
    pub has_discriminants: bool,
    pub adt_variant_count: Option<usize>,
    pub values: Vec<Discriminant>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct Discriminant {
    pub variant: u32,
    #[serde(rename = "type")]
    pub ty: u64,
    pub bits: String,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct ProjectionQueries {
    pub typing_env: &'static str,
    pub parents: Vec<ProjectionParent>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct ProjectionParent {
    pub variant: Option<usize>,
    pub layout: u64,
    pub fields: Vec<ProjectionField>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct ProjectionField {
    pub index: usize,
    #[serde(rename = "type")]
    pub ty: u64,
    pub layout: u64,
}
