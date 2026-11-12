//! Semantic leaves shared by the exported graph pools.
use serde::Serialize;

#[derive(Clone, Debug, Serialize)]
pub(crate) struct Definition {
    #[serde(rename = "crate")]
    pub crate_index: u32,
    pub index: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body_track_caller: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adt_drop: Option<AdtDropMaterial>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generic_template: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub alias_declaration: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adt_declaration: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw_path: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_environment: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub function_abi_material: Option<FunctionAbiMaterial>,
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct FunctionAbiMaterial {
    pub never_unwind: bool,
    pub foreign_item: bool,
    pub drop_glue: bool,
    pub rustc_no_writable: bool,
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct AbiSessionMaterial {
    pub panic: &'static str,
    pub panic_in_drop: &'static str,
    pub optimization: &'static str,
    pub llvm_writable: bool,
    pub box_noalias: bool,
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct AdtDropMaterial {
    pub manually_drop: bool,
    pub destructor: Option<u64>,
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
    pub ctxt: String,
    pub file: u64,
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

/// Exact presentation text, shared across source spans and backtrace positions.
/// Debug filenames and remapped display filenames have different consumers;
/// only identical strings share an ID, without normalizing either spelling.
#[derive(Default)]
pub(crate) struct Files {
    ids: std::collections::HashMap<String, u64>,
    values: Vec<String>,
}
impl Files {
    pub fn intern(&mut self, text: String) -> u64 {
        if let Some(&id) = self.ids.get(&text) {
            return id;
        }
        let id = self.values.len() as u64;
        self.ids.insert(text.clone(), id);
        self.values.push(text);
        id
    }
    pub fn finish(self) -> Vec<String> {
        self.values
    }
}

#[cfg(test)]
mod file_tests {
    use super::Files;
    #[test]
    fn exact_text_shares_ids_across_uses_without_normalizing_paths() {
        let mut files = Files::default();
        assert_eq!(files.intern("src/main.rs".into()), 0);
        assert_eq!(files.intern("src/other.rs".into()), 1);
        assert_eq!(files.intern("src/main.rs".into()), 0);
        assert_eq!(files.intern("Real(\"src/main.rs\")".into()), 2);
        assert_eq!(files.intern("src/../src/main.rs".into()), 3);
        assert_eq!(files.intern("src/other.rs".into()), 1);
        assert_eq!(files.finish(), vec!["src/main.rs", "src/other.rs",
            "Real(\"src/main.rs\")", "src/../src/main.rs"]);
    }
}
