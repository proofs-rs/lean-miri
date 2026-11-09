//! Semantic leaves shared by the exported graph pools.
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
pub(crate) struct Definition {
    #[serde(rename = "crate")]
    pub crate_index: u32,
    pub index: u32,
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct DebugPayload {
    pub status: &'static str,
    pub rustc_debug: String,
}
impl DebugPayload {
    pub fn new(value: &impl std::fmt::Debug) -> Self {
        Self {
            status: "debug_payload",
            rustc_debug: format!("{value:?}"),
        }
    }
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct Position {
    pub line: usize,
    pub column: usize,
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct Span {
    pub is_dummy: bool,
    pub lo: u32,
    pub hi: u32,
    pub ctxt: DebugPayload,
    pub file: DebugPayload,
    pub start: Position,
    pub end: Position,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum BoundRegionKind {
    Anonymous,
    NamedForPrinting { name: String },
    Named { def_id: u64, def_path: String },
    ClosureEnvironment,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum BoundIndex {
    Bound { debruijn_index: u32 },
    Canonical,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum LateParameter {
    Anonymous { index: u32 },
    NamedAnonymous { index: u32, name: String },
    Named { def_id: u64, def_path: String },
    ClosureEnvironment,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum Region {
    EarlyParameter {
        index: u32,
        name: String,
    },
    Bound {
        index_kind: BoundIndex,
        variable_index: u32,
        bound_kind: BoundRegionKind,
    },
    LateParameter {
        scope_def_id: u64,
        scope_def_path: String,
        parameter: LateParameter,
    },
    Static,
    Placeholder {
        universe: u32,
        variable_index: u32,
        bound_kind: BoundRegionKind,
    },
    Erased,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum BoundTypeKind {
    Anonymous,
    Parameter { def_id: u64 },
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum BoundVariable {
    Type { type_kind: BoundTypeKind },
    Region { region_kind: BoundRegionKind },
    Const,
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub(crate) enum GenericArgument {
    Type(u64),
    Lifetime(Region),
    Const(u64),
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum ValTree {
    Leaf {
        size_bytes: u64,
        bits_unsigned: String,
    },
    Branch {
        elements: Vec<u64>,
    },
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum TypeConstant {
    Value {
        #[serde(rename = "type")]
        ty: u64,
        value: ValTree,
    },
    Alias {
        rigidity: &'static str,
        alias_kind: &'static str,
        def_id: u64,
        def_path: String,
        generic_args: Vec<GenericArgument>,
    },
    Expression {
        expression_kind: &'static str,
        operator: Option<&'static str>,
        arguments: Vec<GenericArgument>,
    },
}
