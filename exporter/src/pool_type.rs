//! Semantic type graph stored while collecting compiler facts.
use crate::pool_values::{BoundVariable, GenericArgument, Region};
use serde::Serialize;
#[derive(Clone, Debug, Serialize)]
pub(super) struct Type {
    pub type_id: u64,
    pub validation_rank: usize,
    pub display: String,
    pub shape: Shape,
    pub source_layout: SourceLayout,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct SourceLayout {
    pub normalized_type: u64,
    pub closure_upvars: Vec<u64>,
    pub variant_discriminants: Vec<String>,
    pub simd: Option<Simd>,
    pub scalable_vectors: Option<u64>,
    pub special_float: Option<&'static str>,
    pub is_x87_f80: bool,
    pub cfi_encoding: Option<String>,
    pub coroutine: Option<SourceCoroutineLayout>,
    pub variances: Vec<crate::pool_body::Variance>,
    pub is_unsafe_cell: bool,
    pub is_unsafe_pinned: bool,
    pub is_manually_drop: bool,
    pub is_maybe_uninit: bool,
    pub is_phantom_data: bool,
    pub is_box: bool,
    pub is_global_allocator: bool,
    pub is_c_void: bool,
    pub is_maybe_dangling: bool,
    pub nonnull_optimization_guaranteed: bool,
    pub definition: Option<u64>,
    pub item_name: Option<String>,
    pub capture_names: Option<Vec<Option<String>>>,
    pub has_destructor: bool,
    pub is_dyn_metadata: bool,
    pub type_id_hash: Option<String>,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct SourceCoroutineLayout {
    pub movability: &'static str,
    pub trait_fields: Vec<SourceCoroutineTraitField>,
    pub saved_types: Vec<u64>,
    pub locals: Vec<u64>,
    pub prefix: Vec<u64>,
    pub variants: Vec<Vec<usize>>,
    pub conflicts: Vec<Vec<usize>>,
    pub seed: u64,
}
#[derive(Clone, Debug, Serialize)]
pub(super) struct SourceCoroutineTraitField {
    pub r#type: u64,
    pub ignore_for_traits: bool,
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
    pub splatted: Option<u8>,
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
pub(super) struct Simd {
    pub count: u64,
    pub element: u64,
}
