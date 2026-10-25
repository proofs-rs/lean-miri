#![feature(rustc_private)]

mod cast_queries;
mod covariance_queries;
mod foreign_symbols;
mod global_byte_queries;
mod intrinsic_symbol_queries;
mod intrinsic_value_queries;
mod libc_type_layouts;
mod main_queries;
mod named_constants;
mod named_statics;
mod native_signature_queries;
mod panic_queries;
mod producer;
mod projection_queries;
mod retag_queries;
mod shim_abi;
mod startup_queries;
mod windows_constants;
mod windows_type_layouts;

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_attr_ir;
extern crate rustc_codegen_ssa;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_structures;
extern crate rustc_symbol_mangling;
extern crate rustc_target;

use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface;
use rustc_middle::mir::interpret::{AllocId, CTFE_ALLOC_SALT, GlobalAlloc};
use rustc_middle::ty::{self, ExistentialPredicateStableCmpExt, TyCtxt, TypeVisitableExt};
use rustc_span::Pos;
use serde_json::{Value, json};

const EXPECTED_RUSTC_COMMIT: &str = "8144389c895da997dbdecaa635e41d6a50be6ffd";
const MIRI_COMMIT: &str = "7fa591d7d4dd9af8154becbc8332f8096f8323b1";

struct Options {
    output: PathBuf,
    rustc_args: Vec<String>,
    root_paths: Vec<String>,
}

struct ExportCallbacks {
    output: PathBuf,
    root_paths: Vec<String>,
    rustc_version: String,
    document: Option<Value>,
    invocation: Option<Value>,
    write_during_analysis: bool,
    continue_compilation: bool,
    export_error: Option<String>,
}

/// Compilation-scoped identities for the actual interned rustc types.
/// The numeric IDs are serialization-local and deliberately carry no claim of
/// cross-compilation stability. Type graph nodes live in `type_nodes`; MIR
/// payloads refer to them by `type_id`.
#[derive(Default)]
struct ExportContext<'tcx> {
    type_ids: HashMap<rustc_middle::ty::Ty<'tcx>, u64>,
    /// Types demanded by serialized source MIR/signatures/metadata. Compiler
    /// query constructors can create type nodes without adding them here.
    runtime_type_query_demands: HashSet<rustc_middle::ty::Ty<'tcx>>,
    runtime_type_query_suppression: usize,
    type_nodes: BTreeMap<u64, Value>,
    type_nodes_in_progress: HashSet<rustc_middle::ty::Ty<'tcx>>,
    next_type_id: u64,
    allocation_ids: HashMap<AllocId, u64>,
    allocation_nodes: BTreeMap<u64, Value>,
    allocations_in_progress: HashSet<AllocId>,
    next_allocation_id: u64,
    instance_ids: HashMap<ty::Instance<'tcx>, u64>,
    /// DropGlue(None) identities first discovered as runtime type-query facts
    /// have no operation and should not seed ABI/MIR query closure by themselves.
    /// A real source use upgrades them in `register_instance`.
    runtime_query_only_empty_drops: HashSet<ty::Instance<'tcx>>,
    /// Instances discovered only while reproducing symbol lookup need their
    /// mono identity, but not the unrelated caller-location/target-feature
    /// query family. Remove them when a real MIR demand upgrades the entry.
    symbol_only_instances: HashSet<ty::Instance<'tcx>>,
    pending_instances: Vec<ty::Instance<'tcx>>,
    emitted_instances: HashSet<ty::Instance<'tcx>>,
    next_instance_id: u64,
    predicate_ids: HashMap<ty::PolyExistentialPredicate<'tcx>, u64>,
    pending_predicates: Vec<ty::PolyExistentialPredicate<'tcx>>,
    instance_abi_requests: HashSet<(ty::Instance<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
    caller_location_span_set: HashSet<rustc_span::Span>,
    caller_location_spans: Vec<rustc_span::Span>,
    cast_unsize_requests: HashSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    vtable_query_requests: HashSet<(
        ty::Ty<'tcx>,
        &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    )>,
    /// Exact type pairs which Miri's transmute/subtype cast path passes to
    /// rustc's `mir_assign_valid_types`, even when their normalized types do
    /// not share the finite identity-group query domain.
    covariance_query_requests: HashSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    cast_box_requests: HashSet<ty::Ty<'tcx>>,
    fn_pointer_abi_requests: HashSet<(ty::Ty<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
}

impl<'tcx> ExportContext<'tcx> {
    fn predicate_id(&mut self, predicate: ty::PolyExistentialPredicate<'tcx>) -> u64 {
        if let Some(id) = self.predicate_ids.get(&predicate) {
            return *id;
        }
        let id = self.pending_predicates.len() as u64;
        self.pending_predicates.push(predicate);
        self.predicate_ids.insert(predicate, id);
        id
    }
    fn type_id(&mut self, ty: rustc_middle::ty::Ty<'tcx>) -> u64 {
        if let Some(id) = self.type_ids.get(&ty) {
            return *id;
        }
        let id = self.next_type_id;
        self.next_type_id += 1;
        self.type_ids.insert(ty, id);
        id
    }

    fn allocation_id(&mut self, alloc_id: AllocId) -> u64 {
        if let Some(id) = self.allocation_ids.get(&alloc_id) {
            return *id;
        }
        let id = self.next_allocation_id;
        self.next_allocation_id += 1;
        self.allocation_ids.insert(alloc_id, id);
        id
    }

    fn register_instance(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        self.runtime_query_only_empty_drops.remove(&instance);
        self.symbol_only_instances.remove(&instance);
        if let Some(id) = self.instance_ids.get(&instance) {
            // An identity-only symbol-table registration may later become
            // reachable from an actual MIR call. Upgrade it into the normal
            // body fixpoint on demand.
            if !self.emitted_instances.contains(&instance)
                && !self.pending_instances.contains(&instance)
            {
                self.pending_instances.push(instance);
            }
            return *id;
        }
        let id = self.next_instance_id;
        self.next_instance_id += 1;
        self.instance_ids.insert(instance, id);
        self.pending_instances.push(instance);
        id
    }

    /// Register compiler identity without eagerly querying MIR. Miri resolves
    /// exported-symbol identities during lookup and only calls `load_mir` for
    /// the selected function. Some rustc symbols have no MIR (and querying
    /// them eagerly can ICE), so callers must request a body separately.
    fn register_instance_identity(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        if let Some(id) = self.instance_ids.get(&instance) {
            return *id;
        }
        let id = self.next_instance_id;
        self.next_instance_id += 1;
        self.instance_ids.insert(instance, id);
        self.symbol_only_instances.insert(instance);
        id
    }
}

fn rustc_commit_from(rustc: &OsStr) -> Result<String, String> {
    let output = Command::new(rustc)
        .arg("--version")
        .arg("--verbose")
        .output()
        .map_err(|e| format!("cannot execute selected rustc: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "selected rustc --version --verbose failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: ").map(str::to_owned))
        .ok_or_else(|| format!("selected rustc did not report commit-hash: {stdout}"))
}

fn resolve_executable(executable: &OsStr) -> Option<String> {
    let path = Path::new(executable);
    if path.components().count() > 1 {
        return path
            .canonicalize()
            .ok()
            .map(|resolved| resolved.to_string_lossy().into_owned());
    }
    env::var_os("PATH").and_then(|search_path| {
        env::split_paths(&search_path).find_map(|directory| {
            let candidate = directory.join(path);
            if !candidate.is_file() {
                return None;
            }
            candidate
                .canonicalize()
                .ok()
                .map(|resolved| resolved.to_string_lossy().into_owned())
        })
    })
}

fn rustc_version_line_from(rustc: &OsStr) -> Result<String, String> {
    let output = Command::new(rustc)
        .arg("--version")
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn rustc_host_from(rustc: &OsStr) -> Result<String, String> {
    let output = Command::new(rustc)
        .arg("--version")
        .arg("--verbose")
        .output()
        .map_err(|error| format!("cannot read pinned rustc host: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "pinned rustc --version --verbose failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(str::to_owned))
        .ok_or_else(|| "pinned rustc version did not contain a host triple".into())
}

/// The extern rustc_private crates are linked to hashed shared libraries.
/// Verify that the libraries actually mapped into this process are beneath
/// the sysroot whose rustc build.rs checked against the pin.
fn loaded_rustc_driver_is_pinned() -> Result<(), String> {
    #[cfg(target_os = "linux")]
    {
        let expected = fs::canonicalize(env!("LEAN_MIRI_PINNED_RUSTC_SYSROOT"))
            .map_err(|error| format!("cannot canonicalize pinned rustc sysroot: {error}"))?;
        let maps = fs::read_to_string("/proc/self/maps")
            .map_err(|error| format!("cannot inspect loaded rustc driver libraries: {error}"))?;
        let mut saw_driver = false;
        for line in maps.lines() {
            let Some(path) = line.split_whitespace().last() else {
                continue;
            };
            if !path.contains("/librustc_driver-") && !path.contains("/librustc_driver_impl-") {
                continue;
            }
            let path = fs::canonicalize(path).map_err(|error| {
                format!("cannot canonicalize loaded compiler library {path}: {error}")
            })?;
            saw_driver = true;
            if !path.starts_with(&expected) {
                return Err(format!(
                    "loaded rustc driver library {} is outside pinned sysroot {}",
                    path.display(),
                    expected.display()
                ));
            }
        }
        if !saw_driver {
            return Err("no dynamically loaded rustc_driver library found in process maps".into());
        }
        Ok(())
    }
    #[cfg(not(target_os = "linux"))]
    {
        Err("runtime verification of the loaded rustc_driver is implemented only on Linux".into())
    }
}

fn parse_args(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let mut args = args.into_iter();
    let mut output = None;
    let mut root_paths = Vec::new();
    let mut rustc_args = Vec::new();
    while let Some(arg) = args.next() {
        if arg == "--output" {
            output = Some(PathBuf::from(
                args.next().ok_or("--output requires a path")?,
            ));
        } else if arg == "--root" {
            root_paths.push(
                args.next()
                    .ok_or("--root requires an exact rustc def-path")?,
            );
        } else if arg == "--help" || arg == "-h" {
            println!(
                "Usage:\n  lean-miri-mir-exporter --output FILE [--root DEF-PATH]... [--] RUSTC-ARG...\n  lean-miri-mir-exporter --cargo CARGO-ARGS...\n\nDirect mode exports typed MIR and stops after analysis. Optional --root selects exact non-generic local def-path roots and emits their reachable structural closure. Cargo mode acts as a rustc wrapper, writes one JSON file per compiled crate, and continues normal codegen/metadata emission. Both require the pinned rustc revision."
            );
            std::process::exit(0);
        } else if arg == "--" {
            rustc_args.extend(args);
            break;
        } else {
            rustc_args.push(arg);
        }
    }
    let output = output.ok_or("missing --output FILE")?;
    if rustc_args.is_empty() {
        return Err("no rustc input or arguments provided".into());
    }
    if !rustc_args.iter().any(|arg| arg.starts_with("--edition")) {
        rustc_args.push("--edition=2024".into());
    }
    if !rustc_args
        .iter()
        .any(|arg| arg.starts_with("-Zmir-opt-level"))
    {
        rustc_args.push("-Zmir-opt-level=0".into());
    }
    Ok(Options {
        output,
        rustc_args,
        root_paths,
    })
}

fn is_required_trait_method<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return false;
    };
    matches!(
        tcx.hir_node_by_def_id(local),
        rustc_hir::Node::TraitItem(rustc_hir::TraitItem {
            kind: rustc_hir::TraitItemKind::Fn(_, rustc_hir::TraitFn::Required(_)),
            ..
        })
    )
}

fn has_local_hir_body<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::DefId) -> bool {
    match def_id.as_local() {
        Some(local) => tcx.hir_node_by_def_id(local).body_id().is_some(),
        None => false,
    }
}

fn body_uses_promoted<'tcx>(body: &rustc_middle::mir::Body<'tcx>) -> bool {
    struct PromotedUse(bool);
    impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for PromotedUse {
        fn visit_const_operand(
            &mut self,
            constant: &rustc_middle::mir::ConstOperand<'tcx>,
            location: rustc_middle::mir::Location,
        ) {
            if matches!(
                constant.const_,
                rustc_middle::mir::Const::Unevaluated(value, _) if value.promoted.is_some()
            ) {
                self.0 = true;
            }
            self.super_const_operand(constant, location);
        }
    }
    let mut visitor = PromotedUse(false);
    rustc_middle::mir::visit::Visitor::visit_body(&mut visitor, body);
    visitor.0
}

fn select_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_definitions: &[LocalDefId],
    requested_paths: &[String],
) -> Result<Vec<LocalDefId>, String> {
    let mut selected = Vec::new();
    for requested in requested_paths {
        let matches = local_definitions
            .iter()
            .copied()
            .filter(|def_id| tcx.def_path_str(def_id.to_def_id()) == *requested)
            .collect::<Vec<_>>();
        let [def_id] = matches.as_slice() else {
            return Err(if matches.is_empty() {
                format!("--root {requested:?} did not resolve to a local MIR body")
            } else {
                format!("--root {requested:?} is ambiguous; pass a fully qualified rustc def-path")
            });
        };
        let def_id = *def_id;
        let def = def_id.to_def_id();
        if !tcx.is_mir_available(def) || is_required_trait_method(tcx, def) {
            return Err(format!("--root {requested:?} has no available MIR body"));
        }
        let body = tcx.instance_mir(ty::InstanceKind::Item(def));
        if body.is_polymorphic {
            return Err(format!(
                "--root {requested:?} is generic; rooted export currently requires a non-generic named body"
            ));
        }
        if !selected.contains(&def_id) {
            selected.push(def_id);
        }
    }
    Ok(selected)
}

fn rooted_closure_obligations(document: &Value) -> Vec<Value> {
    fn probe_matches_query(document: &Value, cast: &serde_json::Map<String, Value>) -> bool {
        let Some(query) = cast
            .get("vtable_query")
            .filter(|query| query.get("status").and_then(Value::as_str) == Some("supported"))
        else {
            return false;
        };
        let Some(probe) = cast.get("vtable_probe").filter(|probe| {
            probe.get("status").and_then(Value::as_str) == Some("incomplete")
                && probe.get("kind").and_then(Value::as_str) == Some("symbolic_vtable_allocation")
        }) else {
            return false;
        };
        let _ = probe;
        let Some(query_id) = query.get("query_id").and_then(Value::as_u64) else {
            return false;
        };
        let Some(rows) = document
            .get("compiler_vtable_queries")
            .and_then(Value::as_array)
        else {
            return false;
        };
        let Some(row) = rows.get(query_id as usize).filter(|row| {
            row.get("query_id").and_then(Value::as_u64) == Some(query_id)
                && row.get("status").and_then(Value::as_str) == Some("supported")
        }) else {
            return false;
        };
        let type_id = |value: &Value| value.get("type_id").and_then(Value::as_u64);
        if type_id(query.get("input_type").unwrap_or(&Value::Null))
            != type_id(row.get("input_type").unwrap_or(&Value::Null))
        {
            return false;
        }
        let pred_ids = |value: &Value| {
            value.as_array().map(|items| {
                items
                    .iter()
                    .map(|item| item.get("predicate_id").and_then(Value::as_u64))
                    .collect::<Option<Vec<_>>>()
            })
        };
        if pred_ids(query.get("input_predicates").unwrap_or(&Value::Null))
            != pred_ids(row.get("input_predicates").unwrap_or(&Value::Null))
        {
            return false;
        }
        if type_id(query.get("source_tail_type").unwrap_or(&Value::Null))
            != type_id(query.get("input_type").unwrap_or(&Value::Null))
        {
            return false;
        }
        let Some(cast_rows) = document
            .get("compiler_cast_queries")
            .and_then(Value::as_array)
        else {
            return false;
        };
        let full_pair = cast_rows.iter().any(|cast_row| {
            cast_row.get("query_kind").and_then(Value::as_str) == Some("lockstep_tails")
                && cast_row.get("status").and_then(Value::as_str) == Some("supported")
                && type_id(cast_row.get("input_source").unwrap_or(&Value::Null))
                    == type_id(query.get("source_type").unwrap_or(&Value::Null))
                && type_id(cast_row.get("input_target").unwrap_or(&Value::Null))
                    == type_id(query.get("target_type").unwrap_or(&Value::Null))
        });
        let pointee_pair = cast_rows.iter().any(|cast_row| {
            let value = cast_row.get("value").unwrap_or(&Value::Null);
            cast_row.get("query_kind").and_then(Value::as_str) == Some("lockstep_tails")
                && cast_row.get("status").and_then(Value::as_str) == Some("supported")
                && type_id(cast_row.get("input_source").unwrap_or(&Value::Null))
                    == type_id(query.get("source_pointee_type").unwrap_or(&Value::Null))
                && type_id(cast_row.get("input_target").unwrap_or(&Value::Null))
                    == type_id(query.get("target_pointee_type").unwrap_or(&Value::Null))
                && type_id(value.get("source_tail").unwrap_or(&Value::Null))
                    == type_id(query.get("source_tail_type").unwrap_or(&Value::Null))
                && type_id(value.get("target_tail").unwrap_or(&Value::Null))
                    == type_id(query.get("target_tail_type").unwrap_or(&Value::Null))
        });
        full_pair && pointee_pair
    }
    fn visit_probe(
        document: &Value,
        value: &Value,
        path: &str,
        obligations: &mut BTreeMap<String, Value>,
        references: &mut Vec<(String, u64)>,
    ) {
        if let Value::Object(object) = value {
            // The probe's root status describes a diagnostic-only CTFE attempt;
            // all children still participate in ordinary obligation checking.
            for (key, child) in object {
                if key != "status" {
                    visit(
                        document,
                        child,
                        &format!("{path}.{key}"),
                        obligations,
                        references,
                    );
                }
            }
        } else {
            visit(document, value, path, obligations, references);
        }
    }
    fn visit(
        document: &Value,
        value: &Value,
        path: &str,
        obligations: &mut BTreeMap<String, Value>,
        references: &mut Vec<(String, u64)>,
    ) {
        match value {
            Value::Object(object) => {
                if object.get("status").and_then(Value::as_str) == Some("debug_payload") {
                    return;
                }
                if let Some(status) = object.get("status").and_then(Value::as_str)
                    && status != "supported"
                {
                    let kind = object.get("kind").and_then(Value::as_str).unwrap_or("");
                    let reason = object
                        .get("reason")
                        .and_then(Value::as_str)
                        .or_else(|| object.get("error").and_then(Value::as_str))
                        .unwrap_or("");
                    obligations.insert(
                        format!("{path}:{status}:{kind}:{reason}"),
                        json!({"path":path,"status":status,"kind":kind,"reason":reason}),
                    );
                }
                for (key, child) in object {
                    // These are independent query catalogs or original diagnostics,
                    // not edges in the executable MIR/type/layout/allocation graph.
                    // Their statuses remain present in the document and adapters.
                    if key == "normalization_template"
                        || key == "compiler_facts"
                        || key == "constructor_identity"
                    {
                        continue;
                    }
                    if key == "vtable_probe" && probe_matches_query(document, object) {
                        visit_probe(
                            document,
                            child,
                            &format!("{path}.{key}"),
                            obligations,
                            references,
                        );
                        continue;
                    }
                    if ["type_id", "allocation_id", "instance_id"].contains(&key.as_str()) {
                        if let Some(id) = child.as_u64() {
                            references.push((key.clone(), id));
                        }
                    }
                    visit(
                        document,
                        child,
                        &format!("{path}.{key}"),
                        obligations,
                        references,
                    );
                }
            }
            Value::Array(values) => {
                for (index, child) in values.iter().enumerate() {
                    visit(
                        document,
                        child,
                        &format!("{path}[{index}]"),
                        obligations,
                        references,
                    );
                }
            }
            _ => {}
        }
    }
    let mut obligations = BTreeMap::new();
    let mut pending = Vec::new();
    // Roots identify canonical instances, never their unsubstituted templates.
    if let Some(bodies) = document.get("bodies").and_then(Value::as_array) {
        for (index, body) in bodies.iter().enumerate() {
            if let Some(entry) = body.get("entry_instance") {
                visit(
                    document,
                    entry,
                    &format!("bodies[{index}].entry_instance"),
                    &mut obligations,
                    &mut pending,
                );
            }
        }
    }
    let mut seen = HashSet::new();
    while let Some((kind, id)) = pending.pop() {
        if !seen.insert((kind.clone(), id)) {
            continue;
        }
        let table = match kind.as_str() {
            "type_id" => "types",
            "allocation_id" => "allocations",
            "instance_id" => "instances",
            _ => unreachable!(),
        };
        let found = document
            .get(table)
            .and_then(Value::as_array)
            .and_then(|items| {
                items
                    .iter()
                    .enumerate()
                    .find(|(_, value)| value.get(&kind).and_then(Value::as_u64) == Some(id))
            });
        if let Some((index, value)) = found {
            visit(
                document,
                value,
                &format!("{table}[{index}]"),
                &mut obligations,
                &mut pending,
            );
        } else {
            obligations.insert(format!("missing:{kind}:{id}"),json!({"path":table,"status":"unknown","kind":"missing_dependency","reason":format!("missing {kind} {id}")}));
        }
    }
    obligations.into_values().collect()
}

// Retain non-executable catalog failures separately from the rooted structural
// dependency result. Consumers must still discharge each query they actually
// use; a complete structural closure is not execution readiness or UB freedom.
fn catalog_evidence_obligations(document: &Value) -> Vec<Value> {
    fn walk(value: &Value, path: &str, out: &mut Vec<Value>) {
        match value {
            Value::Object(object) => {
                if object.get("status").and_then(Value::as_str) == Some("debug_payload") {
                    return;
                }
                if let Some(status) = object.get("status").and_then(Value::as_str)
                    && status != "supported"
                {
                    out.push(json!({"path":path,"status":status,
                        "kind":object.get("kind"),"reason":object.get("reason")}));
                }
                for (key, child) in object {
                    walk(child, &format!("{path}.{key}"), out)
                }
            }
            Value::Array(items) => {
                for (index, child) in items.iter().enumerate() {
                    walk(child, &format!("{path}[{index}]"), out)
                }
            }
            _ => {}
        }
    }
    let mut result = Vec::new();
    for key in [
        "types",
        "compiler_runtime_queries",
        "compiler_shim_abis",
        "compiler_predicate_queries",
        "compiler_named_shim_abis",
        "compiler_named_types",
        "compiler_runtime_primitives",
        "compiler_named_constants",
        "compiler_cast_queries",
        "compiler_type_name_constants",
        "compiler_caller_location_constants",
        "compiler_panic_queries",
        "compiler_covariance_queries",
        "compiler_global_byte_queries",
        "compiler_native_signature_queries",
        "compiler_retag_queries",
    ] {
        if let Some(value) = document.get(key) {
            walk(value, key, &mut result)
        }
    }
    result
}

fn retained_vtable_probe_diagnostics(document: &Value) -> Vec<Value> {
    fn walk(value: &Value, path: &str, out: &mut Vec<Value>) {
        match value {
            Value::Object(object) => {
                if let Some(probe) = object.get("vtable_probe") {
                    if probe.get("status").and_then(Value::as_str) == Some("incomplete")
                        && probe.get("kind").and_then(Value::as_str)
                            == Some("symbolic_vtable_allocation")
                        && probe.get("salt_policy").and_then(Value::as_str).is_some()
                    {
                        out.push(json!({"path":format!("{path}.vtable_probe"),
                            "status":probe.get("status"),"kind":probe.get("kind"),
                            "reason":probe.get("salt_policy"),"diagnostic_only":true}));
                    }
                }
                for (key, child) in object {
                    walk(child, &format!("{path}.{key}"), out)
                }
            }
            Value::Array(items) => {
                for (index, child) in items.iter().enumerate() {
                    walk(child, &format!("{path}[{index}]"), out)
                }
            }
            _ => (),
        }
    }
    let mut result = Vec::new();
    if let Some(bodies) = document.get("bodies") {
        walk(bodies, "bodies", &mut result)
    }
    if let Some(instances) = document.get("instances") {
        walk(instances, "instances", &mut result)
    }
    result
}

fn mir_phase_json(phase: rustc_middle::mir::MirPhase) -> Value {
    use rustc_middle::mir::{AnalysisPhase as A, MirPhase as M, RuntimePhase as R};
    match phase {
        M::Built => json!({"status":"supported","kind":"built"}),
        M::Analysis(A::Initial) => {
            json!({"status":"supported","kind":"analysis","phase":"initial"})
        }
        M::Analysis(A::PostCleanup) => {
            json!({"status":"supported","kind":"analysis","phase":"post_cleanup"})
        }
        M::Runtime(R::Initial) => json!({"status":"supported","kind":"runtime","phase":"initial"}),
        M::Runtime(R::PostCleanup) => {
            json!({"status":"supported","kind":"runtime","phase":"post_cleanup"})
        }
        M::Runtime(R::Optimized) => {
            json!({"status":"supported","kind":"runtime","phase":"optimized"})
        }
    }
}

fn coroutine_kind_json(kind: rustc_hir::CoroutineKind) -> Value {
    use rustc_hir::{CoroutineDesugaring as D, CoroutineKind as K, CoroutineSource as S};
    match kind {
        K::Desugared(desugaring, source) => json!({
            "status":"supported",
            "kind":"desugared",
            "desugaring":match desugaring { D::Async => "async", D::Gen => "gen", D::AsyncGen => "async_gen" },
            "source":match source { S::Block => "block", S::Closure => "closure", S::Fn => "function" },
        }),
        K::Coroutine(movability) => json!({
            "status":"supported",
            "kind":"coroutine",
            "movability":match movability { rustc_hir::Movability::Static => "static", rustc_hir::Movability::Movable => "movable" },
        }),
    }
}

fn call_source_name(source: rustc_middle::mir::CallSource) -> &'static str {
    use rustc_middle::mir::CallSource as C;
    match source {
        C::OverloadedOperator => "overloaded_operator",
        C::MatchCmp => "match_comparison",
        C::Misc => "miscellaneous_desugaring",
        C::Use => "clone_or_use",
        C::Normal => "normal_call",
    }
}

fn fake_read_cause_json(cause: rustc_middle::mir::FakeReadCause) -> Value {
    use rustc_middle::mir::FakeReadCause as F;
    match cause {
        F::ForMatchGuard => json!({"status":"supported","kind":"match_guard"}),
        F::ForMatchedPlace(def_id) => {
            json!({"status":"supported","kind":"matched_place","hoisted_from":def_id.map(|id|json!(def_json(id.to_def_id())))})
        }
        F::ForGuardBinding => json!({"status":"supported","kind":"guard_binding"}),
        F::ForLet(def_id) => {
            json!({"status":"supported","kind":"let_binding","hoisted_from":def_id.map(|id|json!(def_json(id.to_def_id())))})
        }
        F::ForIndex => json!({"status":"supported","kind":"index"}),
    }
}

fn runtime_check_json(tcx: TyCtxt<'_>, check: rustc_middle::mir::RuntimeChecks) -> Value {
    use rustc_middle::mir::RuntimeChecks as R;
    let (kind, enabled) = match check {
        R::UbChecks => ("ub_checks", check.value(tcx.sess)),
        R::ContractChecks => ("contract_checks", check.value(tcx.sess)),
        R::OverflowChecks => ("overflow_checks", check.value(tcx.sess)),
    };
    json!({"status":"supported","kind":kind,"enabled":enabled})
}

fn bound_region_kind_json(tcx: TyCtxt<'_>, kind: ty::BoundRegionKind<'_>) -> Value {
    use ty::BoundRegionKind as B;
    match kind {
        B::Anon => json!({"status":"supported","kind":"anonymous"}),
        B::NamedForPrinting(name) => {
            json!({"status":"supported","kind":"named_for_printing","name":name.as_str()})
        }
        B::Named(def_id) => {
            json!({"status":"supported","kind":"named","def_id":def_json(def_id),"def_path":tcx.def_path_str(def_id)})
        }
        B::ClosureEnv => json!({"status":"supported","kind":"closure_environment"}),
    }
}

fn region_json(tcx: TyCtxt<'_>, region: ty::Region<'_>) -> Value {
    use ty::RegionKind as R;
    match region.kind() {
        R::ReEarlyParam(param) => json!({
            "status":"supported","kind":"early_parameter","index":param.index,"name":param.name.as_str(),
        }),
        R::ReBound(index_kind, bound) => json!({
            "status":"supported","kind":"bound",
            "index_kind":match index_kind {
                ty::BoundVarIndexKind::Bound(index) => json!({"kind":"bound","debruijn_index":index.as_u32()}),
                ty::BoundVarIndexKind::Canonical => json!({"kind":"canonical"}),
            },
            "variable_index":bound.var.as_u32(),
            "bound_kind":bound_region_kind_json(tcx,bound.kind),
        }),
        R::ReLateParam(param) => {
            let parameter = match param.kind {
                ty::LateParamRegionKind::Anon(index) => json!({"kind":"anonymous","index":index}),
                ty::LateParamRegionKind::NamedAnon(index, name) => {
                    json!({"kind":"named_anonymous","index":index,"name":name.as_str()})
                }
                ty::LateParamRegionKind::Named(def_id) => {
                    json!({"kind":"named","def_id":def_json(def_id),"def_path":tcx.def_path_str(def_id)})
                }
                ty::LateParamRegionKind::ClosureEnv => json!({"kind":"closure_environment"}),
            };
            json!({"status":"supported","kind":"late_parameter","scope_def_id":def_json(param.scope),"scope_def_path":tcx.def_path_str(param.scope),"parameter":parameter})
        }
        R::ReStatic => json!({"status":"supported","kind":"static"}),
        R::ReVar(variable) => {
            json!({"status":"unsupported","kind":"inference_variable","index":variable.as_u32()})
        }
        R::RePlaceholder(placeholder) => json!({
            "status":"supported","kind":"placeholder","universe":placeholder.universe().as_u32(),
            "variable_index":placeholder.bound.var.as_u32(),
            "bound_kind":bound_region_kind_json(tcx,placeholder.bound.kind),
        }),
        R::ReErased => json!({"status":"supported","kind":"erased"}),
        R::ReError(_) => json!({"status":"unsupported","kind":"error"}),
    }
}

// Numeric fields come from the parsed compiler TargetDataLayout. Its private
// address-space inventory and _is_fat bit have no public accessors. Enumerate
// those only from the official LLVM data-layout input, following the pinned
// rustc_abi parser's p/pf directive and instruction-space inheritance rules.
fn runtime_target_data_layout_json(tcx: TyCtxt<'_>) -> Value {
    use rustc_abi::{AddressSpace, Endian};
    let dl = &tcx.data_layout;
    let llvm = tcx.sess.target.data_layout.to_string();
    let mut spaces: Vec<(AddressSpace, bool)> = Vec::new();
    let mut default_fat = false; // TargetDataLayout::default PointerSpec._is_fat.
    for directive in llvm.split('-') {
        let parts = directive.split(':').collect::<Vec<_>>();
        if parts.len() < 3 || !parts[0].starts_with('p') {
            continue;
        }
        let prefix = &parts[0][1..];
        let (prefix, fat) = match prefix.strip_prefix('f') {
            Some(rest) => (rest, true),
            None => (prefix, false),
        };
        let space = if prefix.is_empty() {
            0
        } else {
            // This string was already successfully parsed by pinned rustc.
            prefix
                .parse::<u32>()
                .expect("validated LLVM pointer address space")
        };
        let space = AddressSpace(space);
        if space == dl.default_address_space {
            default_fat = fat;
        } else if let Some(entry) = spaces.iter_mut().find(|entry| entry.0 == space) {
            entry.1 = fat;
        } else {
            spaces.push((space, fat));
        }
    }
    if dl.instruction_address_space != dl.default_address_space
        && !spaces
            .iter()
            .any(|entry| entry.0 == dl.instruction_address_space)
    {
        spaces.push((dl.instruction_address_space, default_fat));
    }
    let spec = |space: AddressSpace, fat: bool| {
        json!({
            "pointer_size_bytes":dl.pointer_size_in(space).bytes(),
            "pointer_align_bytes":dl.pointer_align_in(space).bytes(),
            "pointer_offset_bytes":dl.pointer_offset_in(space).bytes(),
            "is_fat":fat,
        })
    };
    let bound = |space: AddressSpace| match dl.pointer_size_in(space).bits() {
        16 | 32 | 64 => Some(dl.obj_size_bound_in(space)),
        _ => None,
    };
    let complete = bound(dl.default_address_space).is_some()
        && spaces.iter().all(|(space, _)| bound(*space).is_some());
    let address_space_info = spaces
        .iter()
        .map(|(space, fat)| {
            json!({
                "address_space":space.0,"spec":spec(*space,*fat),
                "object_size_bound_bytes":bound(*space),
            })
        })
        .collect::<Vec<_>>();
    json!({
        "status":if complete { "supported" } else { "unsupported" },
        "object_size_bound_obligation":if complete { None } else { Some("pinned rustc object-size query supports only 16/32/64-bit pointer representations") },
        "evidence_path":"rustc_abi/src/lib.rs::TargetDataLayout; TyCtxt::data_layout",
        "llvm_data_layout":llvm,
        "private_inventory_evidence":"p/pf directives and instruction-space inheritance from pinned TargetDataLayout::parse_from_llvm_datalayout_string",
        "alignment_evidence":"pinned TargetDataLayout stores ABI Align only; preferred LLVM alignment entries remain in llvm_data_layout",
        "endian":match dl.endian { Endian::Little => "little", Endian::Big => "big" },
        "pointer_width_bits":dl.pointer_size().bits(),
        "object_size_bound_bytes":bound(dl.default_address_space),
        "i1_align_bytes":dl.i1_align.bytes(),"i8_align_bytes":dl.i8_align.bytes(),
        "i16_align_bytes":dl.i16_align.bytes(),"i32_align_bytes":dl.i32_align.bytes(),
        "i64_align_bytes":dl.i64_align.bytes(),"i128_align_bytes":dl.i128_align.bytes(),
        "f16_align_bytes":dl.f16_align.bytes(),"f32_align_bytes":dl.f32_align.bytes(),
        "f64_align_bytes":dl.f64_align.bytes(),"f128_align_bytes":dl.f128_align.bytes(),
        "aggregate_align_bytes":dl.aggregate_align.bytes(),
        "vector_align":dl.vector_align.iter().map(|(size,align)|json!({"size_bytes":size.bytes(),"align_bytes":align.bytes()})).collect::<Vec<_>>(),
        "default_address_space":dl.default_address_space.0,
        "default_address_space_pointer_spec":spec(dl.default_address_space,default_fat),
        "address_space_info":address_space_info,
        "instruction_address_space":dl.instruction_address_space.0,
        "c_enum_min_size":match dl.c_enum_min_size {
            rustc_abi::Integer::I8 => "I8", rustc_abi::Integer::I16 => "I16",
            rustc_abi::Integer::I32 => "I32", rustc_abi::Integer::I64 => "I64",
            rustc_abi::Integer::I128 => "I128",
        },
    })
}

impl Callbacks for ExportCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let items = tcx.hir_crate_items(());
        let mut local_definitions = items
            .definitions()
            .chain(items.nested_bodies())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        local_definitions.sort_by_key(|def_id| tcx.def_path_str(def_id.to_def_id()));
        let selected_roots = match select_roots(tcx, &local_definitions, &self.root_paths) {
            Ok(roots) => roots,
            Err(error) => {
                self.export_error = Some(error);
                return Compilation::Stop;
            }
        };
        let is_scoped = !selected_roots.is_empty();
        let root_ids = selected_roots
            .iter()
            .map(|def_id| def_id.to_def_id())
            .collect::<HashSet<_>>();
        let mut export_context = ExportContext::default();
        let main_query_roots = local_definitions
            .iter()
            .copied()
            .filter(|def| {
                if is_scoped {
                    root_ids.contains(&def.to_def_id())
                } else {
                    tcx.is_mir_available(def.to_def_id())
                        && !is_required_trait_method(tcx, def.to_def_id())
                }
            })
            .map(|def| def.to_def_id())
            .collect::<Vec<_>>();
        let bodies = local_definitions
            .into_iter()
            .filter(|def_id| {
                if is_scoped {
                    root_ids.contains(&def_id.to_def_id())
                } else {
                    tcx.is_mir_available(def_id.to_def_id())
                        && !is_required_trait_method(tcx, def_id.to_def_id())
                }
            })
            .map(|def_id| export_body(tcx, def_id, &mut export_context))
            .collect::<Vec<_>>();
        // eval.rs main compiler queries must enqueue actual lang_start MIR
        // before the shared reachable-instance traversal.
        let main_queries = main_queries::export(tcx, &mut export_context, &main_query_roots);
        // Canonical primitive identities for runtime array constructors.
        let runtime_primitives = json!({"u8":type_json(&mut export_context,tcx,tcx.types.u8),
            "u16":type_json(&mut export_context,tcx,tcx.types.u16),
            "u32":type_json(&mut export_context,tcx,tcx.types.u32),
            "u64":type_json(&mut export_context,tcx,tcx.types.u64),
            "u128":type_json(&mut export_context,tcx,tcx.types.u128),
            "i8":type_json(&mut export_context,tcx,tcx.types.i8),
            "i16":type_json(&mut export_context,tcx,tcx.types.i16),
            "i32":type_json(&mut export_context,tcx,tcx.types.i32),
            "i64":type_json(&mut export_context,tcx,tcx.types.i64),
            "i128":type_json(&mut export_context,tcx,tcx.types.i128),
            "bool":type_json(&mut export_context,tcx,tcx.types.bool),
            "pointer_tag_integer":type_json(&mut export_context,tcx,{
                use rustc_middle::ty::layout::IntegerExt;
                tcx.data_layout.ptr_sized_integer().to_ty(tcx,false)
            }),
            "usize":type_json(&mut export_context,tcx,tcx.types.usize),
            "isize":type_json(&mut export_context,tcx,tcx.types.isize),
            "unit":type_json(&mut export_context,tcx,tcx.types.unit),
            "unit_pointer_const":type_json(&mut export_context,tcx,ty::Ty::new_imm_ptr(tcx,tcx.types.unit)),
            "unit_pointer_mut":type_json(&mut export_context,tcx,ty::Ty::new_mut_ptr(tcx,tcx.types.unit)),
            "imm_u8_pointer":type_json(&mut export_context,tcx,ty::Ty::new_imm_ptr(tcx,tcx.types.u8)),
            "imm_u8_pointer_pointer":type_json(&mut export_context,tcx,ty::Ty::new_imm_ptr(tcx,ty::Ty::new_imm_ptr(tcx,tcx.types.u8))),
            // Seed the intrinsic's actual result before the finite runtime
            // query domain is captured; late ConstValue export must not leave
            // its &str layout without the corresponding compiler leaves.
            "type_name_result_type":type_json(&mut export_context,tcx,
                ty::Ty::new_imm_ref(tcx,tcx.lifetimes.re_erased,tcx.types.str_)),
            "caller_location_type":if tcx.lang_items().get(rustc_attr_ir::LangItem::PanicLocation).is_some(){
                compiler_fact(type_json(&mut export_context,tcx,tcx.caller_location_ty()))
            }else{unavailable_compiler_fact("missing PanicLocation lang item")},
            "ordering_enum":if tcx.lang_items().get(rustc_attr_ir::LangItem::OrderingEnum).is_some(){
                compiler_fact(type_json(&mut export_context,tcx,tcx.ty_ordering_enum(rustc_span::DUMMY_SP)))
            }else{unavailable_compiler_fact("missing OrderingEnum lang item")}});
        let named_shim_abis = shim_abi::named_signatures(tcx, &mut export_context);
        let named_types = shim_abi::named_types(tcx, &mut export_context);
        let libc_type_layouts = libc_type_layouts::export(tcx, &mut export_context);
        let windows_type_layouts = windows_type_layouts::export(tcx, &mut export_context);
        let mut named_constants = named_constants::export(tcx, &mut export_context);
        if let Some(rows) = named_constants.as_array_mut() {
            rows.extend(windows_constants::export(tcx, &mut export_context));
        }
        let named_statics = named_statics::export(tcx, &mut export_context);
        let shim_abis = shim_abi::export(tcx, &mut export_context);
        panic_queries::register_termination_helpers(tcx, &mut export_context);
        let mut instances = export_reachable_instances(tcx, &mut export_context);
        // Seed erased signature types before the finite runtime-query domain.
        let _ = native_signature_queries::export(tcx, &mut export_context);
        let _ = cast_queries::export(tcx, &mut export_context);
        instances.extend(export_reachable_instances(tcx, &mut export_context));
        let _intrinsic_type_names_seed = intrinsic_value_queries::type_names(tcx, &mut export_context);
        let _caller_location_constants_seed =
            intrinsic_value_queries::caller_locations(tcx, &mut export_context);
        let _ = compiler_vtable_queries_json(tcx, &mut export_context);
        let _predicate_queries_seed = compiler_predicate_queries_json(tcx, &mut export_context);
        let _native_signature_queries_seed = native_signature_queries::export(tcx, &mut export_context);
        let _retag_queries_seed = retag_queries::export(tcx, &export_context);
        let mut internal_target_features = tcx
            .sess
            .internal_target_features
            .iter()
            .map(|name| name.as_str().to_owned())
            .collect::<Vec<_>>();
        internal_target_features.sort();
        let mut root_span = span_json(tcx, rustc_span::DUMMY_SP);
        root_span["is_dummy"] = json!(rustc_span::DUMMY_SP.is_dummy());
        // Every catalog below is a source-demand producer or a projection of
        // accumulated source demands. Recompute the projections until one full
        // round adds no types, predicates, instances, allocations, query keys,
        // spans, or pending MIR. No producer enumerates hypothetical type
        // constructors; generated runtime pointer/ref outputs are suppressed
        // as fresh runtime-query demands.
        let mut runtime_type_queries = Vec::new();
        let mut processed_runtime_type_queries = HashSet::new();
        let trace_catalog_rounds = std::env::var_os("LEAN_MIRI_TRACE_CATALOG_ROUNDS").is_some();
        let mut catalog_round = 0usize;
        let (
            cast_queries,
            vtable_queries,
            vtable_query_ids,
            runtime_virtual_queries,
            runtime_foreign_symbols,
            runtime_caller_instances,
            global_byte_queries,
            symbol_identity_instances,
            instance_abis,
            covariance_queries,
            function_facts,
            predicate_queries,
            native_signature_queries,
            retag_queries,
            intrinsic_type_names,
            caller_location_constants,
        ) = loop {
            catalog_round += 1;
            let round_started = std::time::Instant::now();
            let demands_before = if trace_catalog_rounds {
                Some(export_context.runtime_type_query_demands.clone())
            } else { None };
            if trace_catalog_rounds {
                eprintln!("catalog round {catalog_round} start: types={} demanded={} instances={} pending={} emitted={} processed={}",
                    export_context.type_ids.len(), export_context.runtime_type_query_demands.len(),
                    export_context.instance_ids.len(), export_context.pending_instances.len(),
                    export_context.emitted_instances.len(), processed_runtime_type_queries.len());
            }
            // Most accumulated domains are insertion-only, so cardinalities
            // prove that their keys did not change. These two identity sets
            // can lose members when an actual source request upgrades a
            // metadata identity; compare their contents as well.
            let before_upgradable_identities = (
                export_context.symbol_only_instances.clone(),
                export_context.runtime_query_only_empty_drops.clone(),
            );
            let before = [
                export_context.instance_ids.len(),
                export_context.pending_instances.len(),
                export_context.emitted_instances.len(),
                export_context.type_ids.len(),
                export_context.type_nodes.len(),
                export_context.allocation_ids.len(),
                export_context.allocation_nodes.len(),
                export_context.predicate_ids.len(),
                export_context.pending_predicates.len(),
                export_context.cast_unsize_requests.len(),
                export_context.cast_box_requests.len(),
                export_context.vtable_query_requests.len(),
                export_context.covariance_query_requests.len(),
                export_context.instance_abi_requests.len(),
                export_context.fn_pointer_abi_requests.len(),
                export_context.caller_location_spans.len(),
                export_context.symbol_only_instances.len(),
                export_context.runtime_query_only_empty_drops.len(),
                export_context.runtime_type_query_demands.len(),
                processed_runtime_type_queries.len(),
            ];
            let cast_queries = cast_queries::export(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} cast {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let (vtable_queries, vtable_query_ids) =
                compiler_vtable_queries_json(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} vtable {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let runtime_foreign_symbols = foreign_symbols::export(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} foreign {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let runtime_virtual_queries =
                compiler_runtime_virtual_queries_json(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} virtual {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            runtime_type_queries.extend(
                compiler_runtime_type_queries_json(
                    tcx,
                    &mut export_context,
                    &mut processed_runtime_type_queries,
                )
                .as_array()
                .expect("runtime type queries are an array")
                .iter()
                .cloned(),
            );
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} type {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let runtime_caller_instances =
                compiler_caller_location_queries_json(tcx, &mut export_context);
            let global_byte_queries = global_byte_queries::export(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} global_bytes {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let symbol_identity_instances =
                symbol_identity_instances_json(tcx, &mut export_context);
            let instance_abis = compiler_instance_abis_json(tcx, &mut export_context);
            let covariance_queries = covariance_queries::export(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} covariance {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            let function_facts = compiler_function_facts_json(tcx, &mut export_context);
            let predicate_queries = compiler_predicate_queries_json(tcx, &mut export_context);
            let native_signature_queries =
                native_signature_queries::export(tcx, &mut export_context);
            let retag_queries = retag_queries::export(tcx, &export_context);
            let intrinsic_type_names =
                intrinsic_value_queries::type_names(tcx, &mut export_context);
            let caller_location_constants =
                intrinsic_value_queries::caller_locations(tcx, &mut export_context);
            if trace_catalog_rounds { eprintln!("catalog round {catalog_round} caller_locations {:?} allocations={}", round_started.elapsed(), export_context.allocation_ids.len()); }
            instances.extend(export_reachable_instances(tcx, &mut export_context));
            if trace_catalog_rounds {
                let previous = demands_before.expect("trace captured prior demands");
                let mut new_demands = export_context.runtime_type_query_demands.difference(&previous)
                    .map(|ty| format!("{ty:?}")).collect::<Vec<_>>();
                new_demands.sort();
                eprintln!("catalog round {catalog_round} end {:?}: types={} demanded={} instances={} pending={} emitted={} processed={} new_demands={} samples={:?}",
                    round_started.elapsed(), export_context.type_ids.len(),
                    export_context.runtime_type_query_demands.len(), export_context.instance_ids.len(),
                    export_context.pending_instances.len(), export_context.emitted_instances.len(),
                    processed_runtime_type_queries.len(), new_demands.len(),
                    new_demands.iter().take(12).collect::<Vec<_>>());
            }
            let after = [
                export_context.instance_ids.len(),
                export_context.pending_instances.len(),
                export_context.emitted_instances.len(),
                export_context.type_ids.len(),
                export_context.type_nodes.len(),
                export_context.allocation_ids.len(),
                export_context.allocation_nodes.len(),
                export_context.predicate_ids.len(),
                export_context.pending_predicates.len(),
                export_context.cast_unsize_requests.len(),
                export_context.cast_box_requests.len(),
                export_context.vtable_query_requests.len(),
                export_context.covariance_query_requests.len(),
                export_context.instance_abi_requests.len(),
                export_context.fn_pointer_abi_requests.len(),
                export_context.caller_location_spans.len(),
                export_context.symbol_only_instances.len(),
                export_context.runtime_query_only_empty_drops.len(),
                export_context.runtime_type_query_demands.len(),
                processed_runtime_type_queries.len(),
            ];
            let after_upgradable_identities = (
                export_context.symbol_only_instances.clone(),
                export_context.runtime_query_only_empty_drops.clone(),
            );
            if trace_catalog_rounds {
                let field_names = ["instance_ids", "pending_instances", "emitted_instances", "type_ids",
                    "type_nodes", "allocation_ids", "allocation_nodes", "predicate_ids",
                    "pending_predicates", "cast_unsize", "cast_box", "vtable_queries",
                    "covariance_queries", "instance_abi", "fn_pointer_abi", "caller_spans",
                    "symbol_only", "empty_drops", "type_demands", "processed_type_queries"];
                let mut changed = Vec::new();
                for (index, name) in field_names.iter().enumerate() {
                    if before[index] != after[index] {
                        changed.push(format!("{name}:{}->{}", before[index], after[index]));
                    }
                }
                let symbol_added = after_upgradable_identities.0.difference(&before_upgradable_identities.0)
                    .map(|instance| format!("{instance:?}")).collect::<Vec<_>>();
                let symbol_removed = before_upgradable_identities.0.difference(&after_upgradable_identities.0)
                    .map(|instance| format!("{instance:?}")).collect::<Vec<_>>();
                let empty_added = after_upgradable_identities.1.difference(&before_upgradable_identities.1)
                    .map(|instance| format!("{instance:?}")).collect::<Vec<_>>();
                let empty_removed = before_upgradable_identities.1.difference(&after_upgradable_identities.1)
                    .map(|instance| format!("{instance:?}")).collect::<Vec<_>>();
                eprintln!("catalog round {catalog_round} convergence: changed={changed:?} symbol_added={symbol_added:?} symbol_removed={symbol_removed:?} empty_added={empty_added:?} empty_removed={empty_removed:?}");
            }
            if before == after && before_upgradable_identities == after_upgradable_identities {
                break (
                    cast_queries,
                    vtable_queries,
                    vtable_query_ids,
                    runtime_virtual_queries,
                    runtime_foreign_symbols,
                    runtime_caller_instances,
                    global_byte_queries,
                    symbol_identity_instances,
                    instance_abis,
                    covariance_queries,
                    function_facts,
                    predicate_queries,
                    native_signature_queries,
                    retag_queries,
                    intrinsic_type_names,
                    caller_location_constants,
                );
            }
        };
        instances.extend(symbol_identity_instances);
        let runtime_queries = json!({
            "types": runtime_type_queries,
            "virtual": runtime_virtual_queries,
            "instances": runtime_caller_instances,
            "foreign_symbols": runtime_foreign_symbols,
            "startup": startup_queries::export(tcx)
        });
        let mut document = json!({
            "schema": "lean-miri-rustc-mir",
            "schema_version": 2,
            "producer": {
                "miri_commit": MIRI_COMMIT,
                "rustc_commit": EXPECTED_RUSTC_COMMIT,
                "rustc_version": self.rustc_version,
                "target_triple": tcx.sess.opts.target_triple.to_string(),
                "input_settings":producer::evidence(tcx,self.invocation.as_ref()),
            },
            "runtime_target_data_layout":runtime_target_data_layout_json(tcx),
            "mir_query": "TyCtxt::instance_mir(InstanceKind::Item(def_id)); ordinary runtime function bodies use optimized_mir",
            "completeness": {
                "status": "incomplete",
                "unsupported_payloads_are_explicit": true,
                "unresolved_obligations": [
                    "Local bodies are all emitted as roots, then directly resolved instances are traversed transitively. Instances without MIR, intrinsic bodies, indirect function pointers, and virtual dispatch targets without a concrete operand remain unresolved.",
                    "Reachable instances are normalized with rustc's instance MIR substitution API when possible. A normalization failure keeps the raw template and an explicit unsupported status; this is not a complete enumeration of instances hidden behind indirect calls or virtual dispatch.",
                    "Indirect function pointers and virtual dispatch targets remain unknown unless rustc MIR carries a directly resolvable FnDef operand.",
                    "Static bodies are emitted as local roots and statics reached through constant relocations are decoded, but this is not a complete enumeration of all statics. Each emitted ThreadLocalRef carries its exact DefId, static query result, and initializer result when available; the consumer implements per-thread allocation and destruction semantics.",
                    "The export is a compiler input model, not an implementation or proof of Miri runtime semantics."
                ],
                "notes": [
                    "Every encountered MIR statement and terminator is emitted with a variant tag.",
                    "Diagnostic-only rustc Debug fields are tagged debug_payload; they never substitute for semantic fields marked unsupported, unknown, or incomplete.",
                    "No unsupported MIR operation is omitted or treated as a successful no-op."
                ]
            },
            "types": export_context.type_nodes.into_values().collect::<Vec<_>>(),
            "allocations": export_context.allocation_nodes.into_values().collect::<Vec<_>>(),
            "instances": instances,
            "compiler_runtime_queries": runtime_queries,
            "compiler_named_statics": named_statics,
            "compiler_frame_metadata":compiler_frame_metadata_json(tcx),
            "compiler_abi_layout_schema":"physical_ty_and_layout_v1",
            "compiler_instance_abis":instance_abis,
            "compiler_function_facts":function_facts,
            "compiler_cast_queries":cast_queries,
            "compiler_type_name_constants":intrinsic_type_names,
            "compiler_panic_queries":panic_queries::export(tcx),
            "compiler_native_signature_queries":native_signature_queries,
            "compiler_retag_queries":retag_queries,
            "compiler_covariance_queries":covariance_queries,
            "compiler_global_byte_queries":global_byte_queries,
            "compiler_caller_location_constants":caller_location_constants,
            "compiler_main_queries":main_queries,
            "compiler_runtime_primitives":runtime_primitives,
            "compiler_session_queries":{"runtime_checks":[
                runtime_check_json(tcx,rustc_middle::mir::RuntimeChecks::UbChecks),
                runtime_check_json(tcx,rustc_middle::mir::RuntimeChecks::ContractChecks),
                runtime_check_json(tcx,rustc_middle::mir::RuntimeChecks::OverflowChecks)],
                "internal_target_features":internal_target_features,
                "is_like_wasm":tcx.sess.target.is_like_wasm,
                "target_arch":tcx.sess.target.arch.to_string(),
                "root_span":root_span},
            "compiler_named_shim_abis":named_shim_abis,
            "compiler_named_types":named_types,
            "compiler_libc_type_layouts":libc_type_layouts,
            "compiler_windows_type_layouts":windows_type_layouts,
            "compiler_named_constants":named_constants,
            "compiler_vtable_queries":vtable_queries,
            "compiler_shim_abis":shim_abis,
            "compiler_predicate_queries":predicate_queries,
            "bodies": bodies,
        });
        patch_vtable_query_ids(&mut document, &vtable_query_ids);
        patch_virtual_resolution_candidates(&mut document);
        if is_scoped {
            let roots = selected_roots
                .iter()
                .map(|def_id| {
                    json!({
                        "def_path":tcx.def_path_str(def_id.to_def_id()),
                        "def_id":def_json(def_id.to_def_id()),
                    })
                })
                .collect::<Vec<_>>();
            let obligations = rooted_closure_obligations(&document);
            let mut catalog_obligations = catalog_evidence_obligations(&document);
            catalog_obligations.extend(retained_vtable_probe_diagnostics(&document));
            document["selected_scope"] = json!({
                "kind":"rooted_structural_closure",
                "semantics":"structural_export_closure_only",
                "status":if obligations.is_empty() { "complete" } else { "incomplete" },
                "roots":roots,
                "dependency_policy":"canonical entry instances and transitive MIR/type-shape/layout/allocation references; original templates diagnostic; independent compiler query catalog failures retained separately",
                "retained_catalog_obligations":catalog_obligations,
                "unresolved_obligations":obligations,
            });
        }
        if let Some(invocation) = self.invocation.take() {
            document["invocation"] = invocation;
        }
        if self.write_during_analysis {
            if let Err(error) = write_document(&self.output, &document) {
                self.export_error = Some(error);
                return Compilation::Stop;
            }
            if self.continue_compilation {
                return Compilation::Continue;
            }
        }
        self.document = Some(document);
        if self.continue_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("lean-miri-mir-exporter: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    if env!("LEAN_MIRI_PINNED_RUSTC_COMMIT") != EXPECTED_RUSTC_COMMIT {
        return Err("binary was not built with the configured pinned compiler".into());
    }
    let args = env::args().skip(1).collect::<Vec<_>>();
    match args.first().map(String::as_str) {
        Some("--cargo") => run_cargo(&args[1..]),
        Some("--help") | Some("-h") => {
            let _ = parse_args(args);
            Ok(())
        }
        Some("--output") => run_direct(args),
        Some(_) => run_as_rustc_wrapper(args),
        None => Err("missing arguments; pass --help for usage".into()),
    }
}

fn validate_rustc_pin(rustc: &OsStr) -> Result<String, String> {
    let actual = rustc_commit_from(rustc)?;
    if actual != EXPECTED_RUSTC_COMMIT {
        return Err(format!(
            "refusing compiler revision {actual}; expected pinned rustc {EXPECTED_RUSTC_COMMIT}"
        ));
    }
    loaded_rustc_driver_is_pinned()?;
    rustc_version_line_from(rustc)
}

fn run_direct(args: Vec<String>) -> Result<(), String> {
    let mut options = parse_args(args)?;
    append_miri_target_flags(&mut options.rustc_args)?;
    if !has_flag(&options.rustc_args, "--sysroot") {
        let sysroot=env::var_os("MIRI_SYSROOT").ok_or("direct MIR export requires explicit --sysroot or MIRI_SYSROOT pointing to the pinned Miri metadata sysroot")?;
        options.rustc_args.push("--sysroot".into());
        options
            .rustc_args
            .push(sysroot.to_string_lossy().into_owned());
    }
    let selected_rustc = OsStr::new("rustc");
    let rustc_version = validate_rustc_pin(selected_rustc)?;
    let mut rustc_args = Vec::with_capacity(options.rustc_args.len() + 1);
    rustc_args.push("rustc".to_owned());
    rustc_args.extend(options.rustc_args);
    let invocation = json!({
        "kind":"direct_rustc_driver",
        "rustc_commit":EXPECTED_RUSTC_COMMIT,
        "rustc_executable":resolve_executable(selected_rustc),
        "working_directory":env::current_dir().ok().map(|path|path.to_string_lossy().into_owned()),
        "rustc_args":&rustc_args[1..],
        "rustc_args_fingerprint_fnv1a64":args_fingerprint(&rustc_args[1..]),
        "root_paths":&options.root_paths,
    });
    let mut callbacks = ExportCallbacks {
        output: options.output,
        root_paths: options.root_paths,
        rustc_version,
        document: None,
        invocation: Some(invocation),
        write_during_analysis: false,
        continue_compilation: false,
        export_error: None,
    };
    let status = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::compiler_entrypoint(&rustc_args, &mut callbacks)
    });
    if status != std::process::ExitCode::SUCCESS {
        return Err("pinned rustc driver reported compilation errors".into());
    }
    if let Some(error) = callbacks.export_error {
        return Err(error);
    }
    let document = callbacks
        .document
        .ok_or("rustc completed without after_analysis output")?;
    write_document(&callbacks.output, &document)
}

fn run_as_rustc_wrapper(args: Vec<String>) -> Result<(), String> {
    if args.is_empty() {
        return Err("Cargo rustc wrapper invocation omitted the rustc executable".into());
    }
    let executable =
        env::current_exe().map_err(|error| format!("cannot locate exporter: {error}"))?;
    let pinned_rustc = PathBuf::from(env!("LEAN_MIRI_PINNED_RUSTC_SYSROOT")).join("bin/rustc");
    let first = PathBuf::from(&args[0]);
    let first_is_self = first
        .canonicalize()
        .ok()
        .zip(executable.canonicalize().ok())
        .is_some_and(|(first, executable)| first == executable);
    let (rustc_path, rustc_args) = if first_is_self {
        (pinned_rustc, &args[1..])
    } else if args[0].starts_with('-') {
        (pinned_rustc, args.as_slice())
    } else {
        (first, &args[1..])
    };
    let rustc_version = validate_rustc_pin(rustc_path.as_os_str())?;

    // Cargo asks rustc for version and target queries outside a crate build.
    // Preserve the exact upstream response after checking the compiler pin.
    if !is_crate_compilation(rustc_args) {
        let status = Command::new(&rustc_path)
            .args(rustc_args)
            .status()
            .map_err(|error| format!("cannot execute Cargo's pinned rustc: {error}"))?;
        return if status.success() {
            Ok(())
        } else {
            Err(format!("pinned rustc query exited with {status}"))
        };
    }
    if rustc_args.iter().any(|arg| arg.starts_with('@')) {
        return Err("rustc response files are not supported by the MIR exporter wrapper".into());
    }

    let crate_name = flag_value(rustc_args, "--crate-name")
        .ok_or("Cargo rustc invocation has no --crate-name")?;
    let out_dir =
        flag_value(rustc_args, "--out-dir").ok_or("Cargo rustc invocation has no --out-dir")?;
    let target_crate = flag_value(rustc_args, "--target").is_some();
    let mut rustc_args = rustc_args.to_vec();
    if target_crate {
        append_miri_target_flags(&mut rustc_args)?;
        if !has_flag(rustc_args.as_slice(), "--sysroot") {
            if let Some(sysroot) = env::var_os("MIRI_SYSROOT") {
                rustc_args.push("--sysroot".into());
                rustc_args.push(sysroot.to_string_lossy().into_owned());
            }
        }
    } else {
        append_once(&mut rustc_args, "-Zalways-encode-mir");
        append_mir_opt_zero(&mut rustc_args)?;
        if !has_flag(&rustc_args, "--sysroot") {
            if let Some(sysroot) = env::var_os("MIRI_HOST_SYSROOT") {
                rustc_args.push("--sysroot".into());
                rustc_args.push(sysroot.to_string_lossy().into_owned());
            }
        }
    }
    let output = cargo_export_path(&out_dir, &crate_name, &rustc_args)?;
    let invocation = json!({
        "kind":"cargo_rustc_wrapper",
        "rustc_commit":EXPECTED_RUSTC_COMMIT,
        "rustc_executable":rustc_path.canonicalize().ok().map(|path|path.to_string_lossy().into_owned()).unwrap_or_else(||rustc_path.to_string_lossy().into_owned()),
        "working_directory":env::current_dir().ok().map(|path|path.to_string_lossy().into_owned()),
        "crate_name":crate_name,
        "source_path":rustc_args.iter().find(|arg|arg.ends_with(".rs")),
        "target_crate":target_crate,
        "rustc_args":&rustc_args,
        "rustc_args_fingerprint_fnv1a64":args_fingerprint(&rustc_args),
    });
    let mut driver_args = Vec::with_capacity(rustc_args.len() + 1);
    driver_args.push(rustc_path.to_string_lossy().into_owned());
    driver_args.extend(rustc_args);
    let mut callbacks = ExportCallbacks {
        output,
        root_paths: Vec::new(),
        rustc_version,
        document: None,
        invocation: Some(invocation),
        write_during_analysis: true,
        continue_compilation: true,
        export_error: None,
    };
    let status = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::compiler_entrypoint(&driver_args, &mut callbacks)
    });
    if status != std::process::ExitCode::SUCCESS {
        return Err("pinned rustc driver reported Cargo compilation errors".into());
    }
    if let Some(error) = callbacks.export_error {
        return Err(error);
    }
    Ok(())
}

fn run_cargo(args: &[String]) -> Result<(), String> {
    let sysroot = PathBuf::from(env!("LEAN_MIRI_PINNED_RUSTC_SYSROOT"));
    let rustc = sysroot.join("bin/rustc");
    validate_rustc_pin(rustc.as_os_str())?;
    let host = rustc_host_from(rustc.as_os_str())?;
    let executable =
        env::current_exe().map_err(|error| format!("cannot locate exporter: {error}"))?;
    let cargo = sysroot.join("bin/cargo");
    let mut cargo_args = args.to_vec();
    if cargo_args.first().is_some_and(|arg| arg == "cargo") {
        cargo_args.remove(0);
    }
    if cargo_args.is_empty() {
        cargo_args.push("build".into());
    }
    let target = cargo_target(&cargo_args).unwrap_or(host);
    if cargo_target(&cargo_args).is_none() {
        let insertion = cargo_args
            .iter()
            .position(|arg| arg == "--")
            .unwrap_or(cargo_args.len());
        cargo_args.insert(insertion, "--target".into());
        cargo_args.insert(insertion + 1, target.clone());
    }

    let cwd =
        env::current_dir().map_err(|error| format!("cannot inspect current directory: {error}"))?;
    let target_base = env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| cwd.join("target"));
    let export_target_dir = target_base.join("lean-miri-exporter-8144389c895d");
    let mut command = Command::new(&cargo);
    command.args(&cargo_args);
    // Match cargo-miri's two-layer dispatch: Cargo invokes the same executable
    // as both RUSTC and RUSTC_WRAPPER. This also catches build scripts which
    // invoke the RUSTC environment variable directly instead of using Cargo's
    // wrapper protocol.
    command.env("RUSTC", &executable);
    command.env("RUSTC_WRAPPER", &executable);
    command.env_remove("RUSTC_WORKSPACE_WRAPPER");
    command.env("CARGO_TARGET_DIR", &export_target_dir);
    let old_path = env::var_os("PATH").unwrap_or_default();
    command.env("PATH", join_paths_prepend(&sysroot.join("bin"), &old_path)?);
    let old_lib_path = env::var_os("LD_LIBRARY_PATH").unwrap_or_default();
    command.env(
        "LD_LIBRARY_PATH",
        join_paths_prepend(&sysroot.join("lib"), &old_lib_path)?,
    );
    let status = command
        .status()
        .map_err(|error| format!("cannot execute pinned Cargo: {error}"))?;
    if !status.success() {
        return Err(format!("Cargo exited with {status}"));
    }
    eprintln!("MIR JSON files are under {}", export_target_dir.display());
    Ok(())
}

fn is_crate_compilation(args: &[String]) -> bool {
    args.iter()
        .any(|arg| arg == "--crate-name" || arg.starts_with("--crate-name="))
        && args
            .iter()
            .any(|arg| arg == "--out-dir" || arg.starts_with("--out-dir="))
        && !args
            .iter()
            .any(|arg| arg == "--version" || arg == "-V" || arg == "-vV")
}

fn flag_value(args: &[String], flag: &str) -> Option<String> {
    args.iter().enumerate().find_map(|(index, arg)| {
        if arg == flag {
            args.get(index + 1).cloned()
        } else {
            arg.strip_prefix(&format!("{flag}=")).map(str::to_owned)
        }
    })
}

fn has_flag(args: &[String], flag: &str) -> bool {
    args.iter()
        .any(|arg| arg == flag || arg.starts_with(&format!("{flag}=")))
}

fn append_once(args: &mut Vec<String>, flag: &str) {
    if !args.iter().any(|arg| arg == flag) {
        args.push(flag.into());
    }
}

fn append_mir_opt_zero(args: &mut Vec<String>) -> Result<(), String> {
    for arg in args.iter() {
        if let Some(level) = arg.strip_prefix("-Zmir-opt-level=") {
            if level != "0" {
                return Err(format!(
                    "MIR export requires -Zmir-opt-level=0, received {arg}"
                ));
            }
            return Ok(());
        }
    }
    args.push("-Zmir-opt-level=0".into());
    Ok(())
}

fn append_miri_target_flags(args: &mut Vec<String>) -> Result<(), String> {
    append_once(args, "--cfg=miri");
    append_once(args, "-Zalways-encode-mir");
    append_once(args, "-Zextra-const-ub-checks");
    append_once(args, "-Zmir-preserve-ub");
    append_mir_opt_zero(args)?;
    append_once(
        args,
        "-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums",
    );
    append_once(args, "-Zmir-enable-passes=-ReferencePropagation,-GVN");
    append_once(args, "-Zdeduplicate-diagnostics=no");
    Ok(())
}

fn cargo_target(args: &[String]) -> Option<String> {
    flag_value(args, "--target")
}

fn cargo_export_path(out_dir: &str, crate_name: &str, args: &[String]) -> Result<PathBuf, String> {
    let directory = Path::new(out_dir).join("lean-miri-mir");
    fs::create_dir_all(&directory)
        .map_err(|error| format!("cannot create {}: {error}", directory.display()))?;
    Ok(directory.join(format!("{}-{}.json", crate_name, args_fingerprint(args))))
}

fn args_fingerprint(args: &[String]) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for arg in args {
        for byte in arg.bytes().chain(std::iter::once(0)) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    format!("{hash:016x}")
}

fn join_paths_prepend(prefix: &Path, rest: &std::ffi::OsStr) -> Result<std::ffi::OsString, String> {
    let mut paths = vec![prefix.to_path_buf()];
    paths.extend(env::split_paths(rest));
    env::join_paths(paths)
        .map_err(|error| format!("cannot construct toolchain search path: {error}"))
}

fn write_document(path: &Path, document: &Value) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(document).map_err(|error| error.to_string())?;
    let parent = path
        .parent()
        .ok_or_else(|| format!("output path {} has no parent", path.display()))?;
    fs::create_dir_all(parent).map_err(|error| {
        format!(
            "cannot create output directory {}: {error}",
            parent.display()
        )
    })?;
    let mut temporary = path.as_os_str().to_os_string();
    temporary.push(format!(".tmp-{}", std::process::id()));
    let temporary = PathBuf::from(temporary);
    fs::write(&temporary, bytes)
        .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path)
        .map_err(|error| format!("cannot install {}: {error}", path.display()))
}

fn export_reachable_instances<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Vec<Value> {
    let mut records = Vec::new();
    let mut cursor = 0;
    while cursor < context.pending_instances.len() {
        let instance = context.pending_instances[cursor];
        cursor += 1;
        if !context.emitted_instances.insert(instance) {
            continue;
        }
        let instance_id = context.instance_ids[&instance];
        let def_id = instance.def.def_id();
        if matches!(
            instance.def,
            ty::InstanceKind::Intrinsic(..) | ty::InstanceKind::LlvmIntrinsic(..)
        ) {
            let fallback = if matches!(instance.def, ty::InstanceKind::Intrinsic(_))
                && tcx
                    .intrinsic(def_id)
                    .is_some_and(|info| !info.must_be_overridden)
                && intrinsic_fallback_is_spec(tcx, def_id)
                && tcx.is_mir_available(def_id)
            {
                let fallback = ty::Instance {
                    def: ty::InstanceKind::Item(def_id),
                    args: instance.args,
                };
                let id = context.register_instance(fallback);
                Some(
                    json!({"instance_id":id,"instance_kind":instance_kind_json(context,tcx,fallback.def),
                    "generic_args":generic_args_json(context,tcx,fallback.args)}),
                )
            } else {
                None
            };
            records.push(json!({
                "instance_id":instance_id,
                "status":"unsupported",
                "kind":"intrinsic_without_mir",
                "fallback_instance":fallback,
                "instance_kind":instance_kind_json(context,tcx,instance.def),
                "def_id":def_json(def_id),
                "def_path":tcx.def_path_str(def_id),
                "generic_args":generic_args_json(context,tcx,instance.args),
                "reason":"Miri executes intrinsic semantics outside a MIR body",
            }));
            continue;
        }
        if let ty::InstanceKind::Virtual(def, slot) = instance.def {
            let function_type = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
            let fn_abi = match tcx.fn_abi_of_instance(
                ty::TypingEnv::fully_monomorphized().as_query_input((instance, ty::List::empty())),
            ) {
                Ok(abi) => compiler_fact(fn_abi_json(context, tcx, abi)),
                Err(error) => {
                    json!({"status":"unsupported","reason":"virtual instance FnAbi query failed","error_debug":format!("{error:?}")})
                }
            };
            records.push(json!({
                "instance_id":instance_id,
                "status":"supported",
                "kind":"virtual_dispatch_target",
                "instance_kind":instance_kind_json(context,tcx,instance.def),
                "def_id":def_json(def),
                "def_path":tcx.def_path_str(def),
                "dispatch_slot":slot,
                "generic_args":generic_args_json(context,tcx,instance.args),
                "body_status":"not_applicable",
                "virtual_identity":{"status":"supported","function_type":type_json(context,tcx,function_type),
                    "fn_abi":fn_abi},
                "reason":"exact virtual method identity and ABI; runtime dispatch selects its concrete implementation from the actual vtable",
            }));
            continue;
        }
        if matches!(instance.def, ty::InstanceKind::Item(_))
            && (!tcx.is_mir_available(def_id) || is_required_trait_method(tcx, def_id))
        {
            records.push(json!({
                "instance_id":instance_id,
                "status":"unsupported",
                "kind":"instance_mir_unavailable",
                "instance_kind":instance_kind_json(context,tcx,instance.def),
                "def_id":def_json(def_id),
                "def_path":tcx.def_path_str(def_id),
                "generic_args":generic_args_json(context,tcx,instance.args),
            }));
            continue;
        }
        let template = tcx.instance_mir(instance.def);
        let typing_env = template.typing_env(tcx);
        let instantiated = instance.try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            typing_env,
            ty::EarlyBinder::bind(tcx, template.clone()),
        );
        let (body_status, body_kind, body_json, body_instantiation) = match instantiated {
            Ok(body) => (
                "supported",
                "instance_mir",
                mir_body_with_constant_queries_json(tcx, &body, instance, true, context),
                json!({"status":"supported","kind":"substituted_and_normalized"}),
            ),
            Err(error) => (
                "unsupported",
                "instance_mir_template",
                mir_body_json(tcx, template, context),
                json!({
                    "status":"unsupported",
                    "kind":"substitution_or_normalization_error",
                    "error_debug":format!("{error:?}"),
                }),
            ),
        };
        // Local HIR bodies own a promoted table even when empty. Imported or
        // compiler-generated MIR can lack that optional table; query it only
        // when the body actually carries a promoted reference.
        let promoted = if has_local_hir_body(tcx, def_id) || body_uses_promoted(template) {
            tcx.promoted_mir(def_id)
                .iter_enumerated()
                .map(|(index, promoted_body)| {
                let promoted_typing_env = promoted_body.typing_env(tcx);
                let promoted_instance = instance.try_instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    promoted_typing_env,
                    ty::EarlyBinder::bind(tcx, promoted_body.clone()),
                );
                match promoted_instance {
                    Ok(body) => json!({
                        "status":"supported",
                        "promoted_index":index.as_u32(),
                        "body_instantiation":{"status":"supported","kind":"substituted_and_normalized"},
                        "body":mir_body_with_constant_queries_json(tcx,&body,instance,true,context),
                    }),
                    Err(error) => json!({
                        "status":"unsupported",
                        "promoted_index":index.as_u32(),
                        "body_instantiation":{
                            "status":"unsupported",
                            "kind":"substitution_or_normalization_error",
                            "error_debug":format!("{error:?}"),
                        },
                        "template_body":mir_body_json(tcx,promoted_body,context),
                    }),
                }
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let status = if body_status == "supported"
            && promoted
                .iter()
                .all(|promoted| promoted["status"] == "supported")
        {
            "supported"
        } else {
            "unsupported"
        };
        records.push(json!({
            "instance_id":instance_id,
            "status":status,
            "kind":body_kind,
            "def_id":def_json(def_id),
            "def_path":tcx.def_path_str(def_id),
            "generic_args":generic_args_json(context,tcx,instance.args),
            "instance_kind":instance_kind_json(context,tcx,instance.def),
            "body_template_is_polymorphic":template.is_polymorphic,
            "instance_args_are_monomorphic":!instance.args.has_non_region_param()
                && !instance.args.has_escaping_bound_vars()
                && !instance.args.has_infer()
                && !instance.args.has_placeholders(),
            "body_instantiation":body_instantiation,
            // Retain the original template as explicitly diagnostic evidence.
            // Serializing its callsites as executable MIR would enqueue generic
            // template callees that are not dependencies of the substituted body.
            "normalization_template":debug_value(template),
            "body":body_json,
            "promoted_bodies":promoted,
        }));
    }
    records
}

/// Preserve exact exported-symbol instance identities that were registered
/// only for source symbol lookup. They are not MIR-demanded, so querying their
/// bodies would be an overreach (and can ICE for compiler-generated symbols),
/// but compiler ABI rows may still refer to these identities. Emit explicit
/// non-runtime identity rows so every reference closes without turning an
/// identity registration into an eager MIR query.
fn symbol_identity_instances_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Vec<Value> {
    let mut identities = context
        .symbol_only_instances
        .iter()
        .filter_map(|instance| {
            context
                .instance_ids
                .get(instance)
                .map(|id| (*id, *instance))
        })
        .collect::<Vec<_>>();
    identities.sort_by_key(|(id, _)| *id);
    identities
        .into_iter()
        .map(|(id, instance)| {
            json!({
                "instance_id":id,
                "status":"unknown",
                "kind":"symbol_identity_only",
                "instance_kind":instance_kind_json(context,tcx,instance.def),
                "def_id":def_json(instance.def.def_id()),
                "def_path":tcx.def_path_str(instance.def.def_id()),
                "generic_args":generic_args_json(context,tcx,instance.args),
                "reason":"exact exported-symbol identity; source MIR was not demanded",
            })
        })
        .collect()
}

// Instance::try_instantiate_mir_and_normalize_erasing_regions expects MIR
// whose parameters belong to that instance's binder. After substitution any
// remaining parameters belong to its caller, not to the callee: binding that
// body again can substitute the wrong parameter or panic in ArgFolder.
// See rustc_middle/ty/instance.rs::args_for_mir_body and the try_* method.
fn mir_body_with_constant_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    instance: ty::Instance<'tcx>,
    already_instantiated: bool,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let normalized = if already_instantiated
        && instance.def.has_polymorphic_mir_body()
        && (body.has_non_region_param()
            || body.has_escaping_bound_vars()
            || body.has_infer()
            || body.has_placeholders())
    {
        json!({"status":"unsupported","kind":"free_caller_parameters_in_instantiated_mir",
            "reason":"MIR has already been substituted; its remaining caller parameters cannot be rebound to this instance's arguments",
            "required_query":"normalization in the complete caller instantiation environment"})
    } else {
        match instance.try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            body.typing_env(tcx),
            ty::EarlyBinder::bind(tcx, body.clone()),
        ) {
            Ok(normalized) => {
                json!({"status":"supported","body":mir_body_json(tcx,&normalized,context)})
            }
            Err(error) => {
                json!({"status":"unsupported","kind":"substitution_or_normalization_error","error_debug":format!("{error:?}")})
            }
        }
    };
    let query_context = json!({"instance_kind":instance_kind_json(context,tcx,instance.def),
        "generic_args":generic_args_json(context,tcx,instance.args),
        "mir_input_phase":if already_instantiated { "already_instantiated" } else { "template" },
        "required_constant_checks":required_constant_checks_json(tcx,body,instance,already_instantiated,context),
        "normalization":normalized});
    let mut result = mir_body_json(tcx, body, context);
    result
        .as_object_mut()
        .expect("body serializer returns an object")
        .insert("constant_query_context".into(), query_context);
    result
}

fn export_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let def_id = local_def_id.to_def_id();
    let body = tcx.instance_mir(ty::InstanceKind::Item(def_id));
    let instance = ty::Instance {
        def: body.source.instance,
        args: ty::GenericArgs::identity_for_item(tcx, def_id),
    };
    // Instance::mono erases lifetime parameters only. Do not fabricate type or
    // const arguments for generic roots, even when optimized MIR ignores them.
    let entry = if !instance.args.has_non_region_param() {
        let canonical = ty::Instance::mono(tcx, def_id);
        Some((context.register_instance(canonical), canonical))
    } else {
        None
    };
    let mut result = mir_body_with_constant_queries_json(tcx, body, instance, false, context);
    let object = result
        .as_object_mut()
        .expect("body serializer returns an object");
    object.insert("entry_instance".into(), match entry {
        Some((id,canonical))=>json!({"status":"supported","instance_id":id,
            "instance_kind":instance_kind_json(context,tcx,canonical.def),
            "generic_args":generic_args_json(context,tcx,canonical.args)}),
        None=>unavailable_compiler_fact("root requires explicit type/const instantiation; Instance::mono cannot invent arguments"),
    });
    object.insert("def_path".into(), json!(tcx.def_path_str(def_id)));
    object.insert("def_id".into(), json!(def_json(def_id)));
    object.insert("is_static".into(), json!(tcx.is_static(def_id)));
    object.insert(
        "thread_local_static".into(),
        json!(tcx.is_thread_local_static(def_id)),
    );
    object.insert(
        "promoted_bodies".into(),
        json!(
            tcx.promoted_mir(def_id)
                .iter_enumerated()
                .map(|(index, promoted)| json!({
                    "promoted_index":index.as_u32(), "body":mir_body_with_constant_queries_json(tcx,promoted,instance,false,context)
                }))
                .collect::<Vec<_>>()
        ),
    );
    result
}

fn mir_body_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    intrinsic_value_queries::collect_spans(tcx, context, body);
    json!({
        "source_instance_kind":instance_kind_json(context,tcx,body.source.instance),
        "preamble_def_span":span_json(tcx,tcx.def_span(body.source.def_id())),
        "backtrace_spans":backtrace_spans_json(tcx,body),
        "source_def_id":def_json(body.source.def_id()),
        "source_promoted":body.source.promoted.map(|value|value.as_u32()),
        "phase": mir_phase_json(body.phase),
        "pass_count": body.pass_count,
        "is_polymorphic": body.has_non_region_param(),
        "source_body_is_polymorphic": body.is_polymorphic,
        "injection_phase": body.injection_phase.map(mir_phase_json),
        "tainted_by_errors": body.tainted_by_errors.map(|value|debug_value(&value)),
        "arg_count": body.arg_count,
        "spread_arg": body.spread_arg.map(|local| local.as_u32()),
        "span": span_json(tcx, body.span),
        "locals": body.local_decls.iter_enumerated().map(|(local, decl)| json!({
            "local": local.as_u32(),
            "mutability": mutability_json(decl.mutability),
            "type": type_json(context, tcx, decl.ty),
            "layout": layout_json(tcx, decl.ty),
            "source_info": source_info_json(tcx, decl.source_info),
            "local_info": debug_value(&decl.local_info),
        })).collect::<Vec<_>>(),
        "basic_blocks": body.basic_blocks.iter_enumerated().map(|(bb, data)| json!({
            "block": bb.as_u32(),
            "is_cleanup": data.is_cleanup,
            "statements": data.statements.iter().map(|statement| json!({
                "source_info": source_info_json(tcx, statement.source_info),
                "kind": statement_json(context, tcx, body, &statement.kind),
            })).collect::<Vec<_>>(),
            "terminator": data.terminator.as_ref().map(|term| json!({
                "source_info": source_info_json(tcx, term.source_info),
                "kind": terminator_json(context, tcx, body, &term.kind),
            })),
        })).collect::<Vec<_>>(),
        "source_scopes": body.source_scopes.iter_enumerated().map(|(scope, data)| json!({
            "scope": scope.as_u32(),
            "parent": data.parent_scope.map(|parent| parent.as_u32()),
            "span": span_json(tcx, data.span),
            "inlined": data.inlined.map(|(instance, callsite)| json!({
                "instance_kind": instance_kind_json(context, tcx, instance.def),
                "generic_args": generic_args_json(context, tcx, instance.args),
                "callsite_span": span_json(tcx, callsite),
                "requires_caller_location": instance.def.requires_caller_location(tcx),
            })),
            "inlined_parent_scope": data.inlined_parent_scope.map(|parent| parent.as_u32()),
            "local_data": debug_value(&data.local_data),
        })).collect::<Vec<_>>(),
        "var_debug_info": body.var_debug_info.iter().map(debug_value).collect::<Vec<_>>(),
        "mentioned_items": body.mentioned_items.as_ref().map(debug_value),
        "required_consts": body.required_consts.as_ref().map(|values| values.iter().map(|v| const_operand_json(context, tcx, body, v)).collect::<Vec<_>>()),
        "user_type_annotations": debug_value(&body.user_type_annotations),
        "coroutine_info": body.coroutine.as_ref().map(|info| json!({
            "status":"unsupported",
            "kind":coroutine_kind_json(info.coroutine_kind),
            "yield_type":info.yield_ty.map(|value|type_json(context, tcx,value)),
            "resume_type":info.resume_ty.map(|value|type_json(context, tcx,value)),
            "coroutine_drop_body":info.coroutine_drop.as_ref().map(|body|mir_body_json(tcx,body,context)),
            "coroutine_drop_async_body":info.coroutine_drop_async.as_ref().map(|body|mir_body_json(tcx,body,context)),
            "coroutine_drop_proxy_async_body":info.coroutine_drop_proxy_async.as_ref().map(|body|mir_body_json(tcx,body,context)),
            "coroutine_layout":{"status":"unsupported","kind":"coroutine_layout","reason":"the compiler coroutine layout is not serialized as a stable typed structure"},
            "reason":"coroutine frame layout and state transitions are not represented by this MIR body serializer"
        })),
    })
}

fn source_info_json(tcx: TyCtxt<'_>, info: rustc_middle::mir::SourceInfo) -> Value {
    json!({ "span": span_json(tcx, info.span), "scope": info.scope.as_u32() })
}

fn span_json(tcx: TyCtxt<'_>, span: rustc_span::Span) -> Value {
    let source_map = tcx.sess.source_map();
    let start = source_map.lookup_char_pos(span.lo());
    let end = source_map.lookup_char_pos(span.hi());
    json!({
        "lo": span.lo().0,
        "hi": span.hi().0,
        "ctxt": debug_value(&span.ctxt()),
        "file": debug_value(&start.file.name),
        "start": { "line": start.line, "column": start.col.to_usize() },
        "end": { "line": end.line, "column": end.col.to_usize() },
    })
}

fn debug_value<T: std::fmt::Debug>(value: &T) -> Value {
    json!({ "status": "debug_payload", "rustc_debug": format!("{value:?}") })
}

fn type_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Value {
    type_json_with_query(context, tcx, ty, ty)
}

/// Serialize the source type while attaching query evidence computed from an
/// explicitly instantiated late-bound-region view. Function signatures retain
/// their original Binder/region graph; only layout and compiler facts consume
/// the query type, which may have those signature-bound regions instantiated
/// with `ReErased`.
fn type_json_with_query<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    query_ty: rustc_middle::ty::Ty<'tcx>,
) -> Value {
    if context.runtime_type_query_suppression == 0 {
        context.runtime_type_query_demands.insert(ty);
    }
    let id = context.type_id(ty);
    if context.type_nodes.contains_key(&id) || context.type_nodes_in_progress.contains(&ty) {
        return json!({"type_id":id});
    }
    context.type_nodes_in_progress.insert(ty);
    let node = type_json_inner(context, tcx, ty, query_ty);
    context.type_nodes_in_progress.remove(&ty);
    context.type_nodes.insert(id, node);
    json!({"type_id":id})
}

/// Serialize a type produced only as a compiler runtime-query result. Its
/// graph still gets exported, but it is not a new source-demand query key.
fn query_generated_type_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Value {
    context.runtime_type_query_suppression += 1;
    let result = type_json(context, tcx, ty);
    context.runtime_type_query_suppression -= 1;
    result
}

fn compiler_fact(value: Value) -> Value {
    json!({"status":"supported","value":value})
}
fn unavailable_compiler_fact(reason: &str) -> Value {
    json!({"status":"unsupported","value":null,"reason":reason})
}

// Query keys are exact interned input types under this explicit typing_env.
// Symbolic caller parameters are not queried as though they were monomorphic.
fn pattern_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    pattern: ty::Pattern<'tcx>,
) -> Value {
    match *pattern.0 {
        ty::PatternKind::Range { start, end } => {
            json!({"status":"supported","kind":"range","start":const_type_json(context,tcx,start),"end":const_type_json(context,tcx,end)})
        }
        ty::PatternKind::Or(patterns) => {
            json!({"status":"supported","kind":"or","patterns":patterns.iter().map(|pattern|pattern_json(context,tcx,pattern)).collect::<Vec<_>>()})
        }
        ty::PatternKind::NotNull => json!({"status":"supported","kind":"not_null"}),
    }
}

fn type_compiler_facts_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    source_input: ty::Ty<'tcx>,
    query_input: ty::Ty<'tcx>,
) -> Value {
    let env = ty::TypingEnv::fully_monomorphized();
    // Query types may come from instantiating a complete function-signature
    // Binder with erased late-bound regions. Do not erase an escaping type or
    // const variable: only region binders are discharged at that boundary.
    let closed = !query_input.has_non_region_param()
        && !query_input.has_escaping_bound_vars()
        && !query_input.has_infer()
        && !query_input.has_placeholders()
        && !query_input.references_error();
    let normalization = if closed {
        Some(tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(query_input)))
    } else {
        None
    };
    let normalized = normalization
        .as_ref()
        .and_then(|result| result.as_ref().ok().copied());
    let missing = || match &normalization {
        Some(Err(error)) => {
            json!({"status":"unsupported","value":null,"reason":"rustc normalization failed","error_debug":format!("{error:?}")})
        }
        _ => unavailable_compiler_fact(
            "requires a complete normalized monomorphic typing environment or required trait lang item",
        ),
    };
    let input = query_input;
    let is_unsafe_cell = matches!(input.kind(),ty::Adt(def,_) if def.is_unsafe_cell());
    let mut booleans = serde_json::Map::new();
    booleans.insert(
        "is_unsafe_cell".into(),
        compiler_fact(json!(is_unsafe_cell)),
    );
    booleans.insert(
        "has_erasable_regions".into(),
        compiler_fact(json!(input.has_erasable_regions())),
    );
    booleans.insert(
        "is_c_void".into(),
        compiler_fact(json!(input.is_c_void(tcx))),
    );
    booleans.insert("is_simd".into(), compiler_fact(json!(input.is_simd())));
    booleans.insert("is_box".into(), compiler_fact(json!(input.is_box())));
    booleans.insert(
        "is_global_box".into(),
        compiler_fact(json!(input.is_box_global(tcx))),
    );
    booleans.insert(
        "is_dynamic".into(),
        compiler_fact(json!(matches!(input.kind(), ty::Dynamic(..)))),
    );
    booleans.insert(
        "is_too_generic".into(),
        compiler_fact(json!(matches!(
            input.kind(),
            ty::Param(..)
                | ty::Alias(..)
                | ty::Bound(..)
                | ty::Placeholder(..)
                | ty::Infer(..)
                | ty::Error(..)
        ))),
    );
    booleans.insert("is_monomorphic".into(), compiler_fact(json!(closed)));
    booleans.insert(
        "is_monomorphic_enough".into(),
        compiler_fact(json!(!input.has_param())),
    );
    booleans.insert(
        "is_like_maybe_dangling".into(),
        compiler_fact(json!(input.is_like_maybe_dangling())),
    );
    booleans.insert(
        "is_freeze".into(),
        match normalized {
            Some(ty)
                if ty.is_trivially_freeze()
                    || tcx
                        .lang_items()
                        .get(rustc_attr_ir::LangItem::Freeze)
                        .is_some() =>
            {
                compiler_fact(json!(ty.is_freeze(tcx, env)))
            }
            _ => missing(),
        },
    );
    booleans.insert(
        "is_unpin".into(),
        match normalized {
            Some(ty)
                if tcx
                    .lang_items()
                    .get(rustc_attr_ir::LangItem::Unpin)
                    .is_some() =>
            {
                compiler_fact(json!(ty.is_unpin(tcx, env)))
            }
            _ => missing(),
        },
    );
    booleans.insert(
        "is_unsafe_unpin".into(),
        match normalized {
            Some(ty)
                if tcx
                    .lang_items()
                    .get(rustc_attr_ir::LangItem::UnsafeUnpin)
                    .is_some() =>
            {
                compiler_fact(json!(ty.is_unsafe_unpin(tcx, env)))
            }
            _ => missing(),
        },
    );
    booleans.insert(
        "needs_drop".into(),
        match normalized {
            Some(ty) => compiler_fact(json!(ty.needs_drop(tcx, env))),
            _ => missing(),
        },
    );
    booleans.insert(
        "opsem_inhabited".into(),
        match normalized {
            Some(ty) => compiler_fact(json!(ty.is_opsem_inhabited(tcx, env))),
            _ => missing(),
        },
    );
    let mut types = serde_json::Map::new();
    types.insert(
        "discriminant_type".into(),
        match normalized {
            Some(ty) => discriminant_type_fact_json(context, tcx, ty),
            _ => missing(),
        },
    );
    types.insert(
        "normalized".into(),
        match normalized {
            Some(ty) => compiler_fact(type_json(context, tcx, ty)),
            _ => missing(),
        },
    );
    types.insert(
        "builtin_deref_explicit".into(),
        compiler_fact(
            input
                .builtin_deref(true)
                .map(|ty| type_json(context, tcx, ty))
                .unwrap_or(Value::Null),
        ),
    );
    types.insert(
        "builtin_deref_implicit".into(),
        compiler_fact(
            input
                .builtin_deref(false)
                .map(|ty| type_json(context, tcx, ty))
                .unwrap_or(Value::Null),
        ),
    );
    types.insert(
        "boxed_type".into(),
        compiler_fact(
            input
                .boxed_ty()
                .map(|ty| type_json(context, tcx, ty))
                .unwrap_or(Value::Null),
        ),
    );
    types.insert(
        "unsafe_binder_erased".into(),
        compiler_fact(match input.kind() {
            ty::UnsafeBinder(bound) => type_json(
                context,
                tcx,
                tcx.instantiate_bound_regions_with_erased((*bound).into()),
            ),
            _ => Value::Null,
        }),
    );
    if let Some(ty) = normalized {
        let tail = tcx.struct_tail_for_codegen(ty, env);
        types.insert(
            "metadata_tail".into(),
            compiler_fact(type_json(context, tcx, tail)),
        );
        types.insert(
            "pointer_metadata_type".into(),
            if matches!(tail.kind(), ty::UnsafeBinder(..)) {
                unavailable_compiler_fact(
                    "rustc ptr_metadata_ty_or_tail does not implement UnsafeBinder",
                )
            } else {
                match ty.ptr_metadata_ty_or_tail(tcx, |ty| tcx.normalize_erasing_regions(env, ty)) {
                    Ok(metadata) => compiler_fact(type_json(context, tcx, metadata)),
                    Err(_) => {
                        unavailable_compiler_fact("rustc could not determine pointer metadata type")
                    }
                }
            },
        );
        booleans.insert(
            "is_sized".into(),
            compiler_fact(json!(ty.is_sized(tcx, env))),
        );
    } else {
        types.insert("metadata_tail".into(), missing());
        types.insert("pointer_metadata_type".into(), missing());
        booleans.insert("is_sized".into(), missing());
    }
    let capture_names = match input.kind() {
        ty::Closure(def, _) | ty::CoroutineClosure(def, _) | ty::Coroutine(def, _) => {
            let names = def
                .as_local()
                .map(|local| {
                    tcx.closure_captures(local)
                        .iter()
                        .map(|capture| {
                            let node = tcx.hir_node(capture.get_root_variable());
                            if let rustc_hir::Node::Pat(pat) = node
                                && let rustc_hir::PatKind::Binding(_, _, ident, _) = pat.kind
                            {
                                Some(ident.name.as_str().to_owned())
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            compiler_fact(json!(names))
        }
        _ => compiler_fact(Value::Null),
    };
    let adt = if let ty::Adt(def, _) = input.kind() {
        Some(
            json!({"definition":def_json(def.did()),"item_name":tcx.item_name(def.did()).as_str(),
            "nonnull_optimization_guaranteed":rustc_attr_ir::find_attr!(tcx,def.did(),RustcNonnullOptimizationGuaranteed)}),
        )
    } else {
        None
    };
    let simd_size_and_type = if !input.is_simd() {
        compiler_fact(Value::Null)
    } else if let Some(ty) = normalized {
        let (count, element) = ty.simd_size_and_type(tcx);
        compiler_fact(json!({"count":count,"element":type_json(context,tcx,element)}))
    } else {
        missing()
    };
    json!({"typing_env":"fully_monomorphized","input_type":type_json(context,tcx,source_input),
        "query_input_type":type_json(context,tcx,query_input),
        "boolean_queries":booleans,"type_queries":types,"adt":adt,"capture_names":capture_names,
        "simd_size_and_type":simd_size_and_type,
        "type_id_hash":intrinsic_symbol_queries::type_id_hash(tcx,input),
        "discriminants":match normalized {Some(ty)=>discriminant_facts_json(context,tcx,ty),_=>missing()},
        "projection_queries":projection_queries::export(tcx,context,input),
        "definition":match input.kind() { ty::Adt(def,_)=>Some(def_json(def.did())),ty::FnDef(def,_)|ty::Closure(def,_)|ty::CoroutineClosure(def,_)|ty::Coroutine(def,_)=>Some(def_json(*def)),_=>None }})
}

fn type_json_inner<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    query_ty: rustc_middle::ty::Ty<'tcx>,
) -> Value {
    let id = context.type_id(ty);
    let shape = match *ty.kind() {
        ty::Bool => json!({ "status": "supported", "kind": "bool" }),
        ty::Char => json!({ "status": "supported", "kind": "char" }),
        ty::Int(kind) => {
            json!({ "status": "supported", "kind": "int", "signed_kind": kind.name_str() })
        }
        ty::Uint(kind) => {
            json!({ "status": "supported", "kind": "uint", "unsigned_kind": kind.name_str() })
        }
        ty::Float(kind) => {
            json!({ "status": "supported", "kind": "float", "float_kind": kind.name_str() })
        }
        ty::Adt(def, args) => {
            let adt = tcx.adt_def(def.did());
            json!({
                "status": "supported",
                "kind": "adt",
                "def_id": format!("{}:{}", def.did().krate.as_u32(), def.did().index.as_u32()),
                "def_path": tcx.def_path_str(def.did()),
                "adt_kind": match adt.adt_kind() {
                    rustc_middle::ty::AdtKind::Struct => "struct",
                    rustc_middle::ty::AdtKind::Union => "union",
                    rustc_middle::ty::AdtKind::Enum => "enum",
                },
                "representation": repr_options_json(&adt.repr()),
                "generic_args": generic_args_json_inner(context, tcx, args),
                "variants": adt.variants().iter_enumerated().map(|(index, variant)| json!({
                    "index": index.as_u32(),
                    "name": variant.name.as_str(),
                    "fields": variant.fields.iter_enumerated().map(|(field_index, field)| json!({
                        "index": field_index.as_u32(),
                        "name": field.name.as_str(),
                        "type": type_json(context, tcx, field.ty(tcx, args).skip_normalization()),
                    })).collect::<Vec<_>>(),
                })).collect::<Vec<_>>(),
            })
        }
        ty::Foreign(def) => json!({
            "status": "supported", "kind": "foreign",
            "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
            "def_path": tcx.def_path_str(def),
        }),
        ty::Str => json!({ "status": "supported", "kind": "str" }),
        ty::Array(element, length) => json!({
            "status": "supported", "kind": "array",
            "element": type_json(context, tcx, element),
            "length": const_type_json(context, tcx, length),
            // This is an exact constructor equality query, not a layout-based
            // approximation and not evaluation of a generic length expression.
            "constructor_identity":match length.try_to_target_usize(tcx) {
                Some(count)=>json!({"status":"supported","count":count,
                    "canonical_value_constructor":ty==ty::Ty::new_array(tcx,element,count)}),
                None=>unavailable_compiler_fact("array length is not a literal target-usize value; canonical runtime constructor equality unavailable"),
            },
        }),
        ty::Pat(base, pattern) => json!({
            "status": "supported", "kind": "pattern_type",
            "base": type_json(context, tcx, base), "pattern":pattern_json(context,tcx,pattern),
        }),
        ty::Slice(element) => {
            json!({ "status": "supported", "kind": "slice", "element": type_json(context, tcx, element) })
        }
        ty::RawPtr(pointee, mutability) => json!({
            "status": "supported", "kind": "raw_pointer",
            "mutability": mutability_json(mutability), "pointee": type_json(context, tcx, pointee),
        }),
        ty::Ref(region, pointee, mutability) => json!({
            "status": "supported", "kind": "reference",
            "region": region_json(tcx, region), "mutability": mutability_json(mutability),
            "pointee": type_json(context, tcx, pointee),
        }),
        ty::FnDef(def, args) => {
            let signature = tcx
                .fn_sig(def)
                .instantiate(tcx, args.skip_binder())
                .skip_normalization();
            let query_signature = tcx.instantiate_bound_regions_with_erased(signature);
            json!({
                "status": "supported", "kind": "function_definition",
                "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
                "def_path": tcx.def_path_str(def),
                "generic_args": generic_args_json_inner(context, tcx, args.skip_binder()),
                "signature": fn_sig_json_with_query(context, tcx, signature.skip_binder(), query_signature),
                "signature_bound_variables": signature.bound_vars().iter().map(|bound|bound_variable_json(tcx,bound)).collect::<Vec<_>>(),
            })
        }
        ty::FnPtr(signature, header) => {
            let signature = signature.with(header);
            let query_signature = tcx.instantiate_bound_regions_with_erased(signature);
            json!({
                "status": "supported", "kind": "function_pointer",
                "signature": fn_sig_json_with_query(context, tcx, signature.skip_binder(), query_signature),
                "signature_bound_variables":signature.bound_vars().iter().map(|bound|bound_variable_json(tcx,bound)).collect::<Vec<_>>(),
            })
        }
        ty::UnsafeBinder(inner) => json!({
            "status": "supported", "kind": "unsafe_binder",
            "inner":type_json(context,tcx,inner.skip_binder()),
            "bound_variables":inner.bound_vars().iter().map(|bound|bound_variable_json(tcx,bound)).collect::<Vec<_>>(),
        }),
        ty::Dynamic(predicates, region) => {
            let principal_predicate = predicates.principal().map(|p| {
                existential_predicate_json(
                    context,
                    tcx,
                    p.map_bound(ty::ExistentialPredicate::Trait),
                )
            });
            let predicates = predicates
                .iter()
                .map(|predicate| {
                    let mut value = existential_predicate_json(context, tcx, predicate);
                    value.as_object_mut().unwrap().insert(
                        "bound_variables".into(),
                        json!(
                            predicate
                                .bound_vars()
                                .iter()
                                .map(|bound| bound_variable_json(tcx, bound))
                                .collect::<Vec<_>>()
                        ),
                    );
                    value
                })
                .collect::<Vec<_>>();
            let region = region_json(tcx, region);
            let supported = region.get("status").and_then(Value::as_str) == Some("supported")
                && predicates
                    .iter()
                    .all(|p| p.get("status").and_then(Value::as_str) == Some("supported"));
            json!({"status":if supported { "supported" } else { "unsupported" },
                "kind":"dynamic_trait_object","region":region,"predicates":predicates,"principal_predicate":principal_predicate})
        }
        ty::Closure(def, args) => json!({
            "status": "supported", "kind": "closure",
            "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
            "def_path": tcx.def_path_str(def), "generic_args": generic_args_json_inner(context, tcx, args),
            "upvar_count":args.as_closure().upvar_tys().len(),
        }),
        ty::CoroutineClosure(def, args) => json!({
            "status": "supported", "kind": "coroutine_closure",
            "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
            "def_path": tcx.def_path_str(def), "generic_args": generic_args_json_inner(context, tcx, args),
        }),
        ty::Coroutine(def, args) => json!({
            "status": "supported", "kind": "coroutine",
            "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
            "def_path": tcx.def_path_str(def), "generic_args": generic_args_json_inner(context, tcx, args),
        }),
        ty::CoroutineWitness(def, args) => json!({
            "status": "unsupported", "kind": "coroutine_witness",
            "def_id": format!("{}:{}", def.krate.as_u32(), def.index.as_u32()),
            "def_path": tcx.def_path_str(def), "generic_args": generic_args_json_inner(context, tcx, args),
        }),
        ty::Never => json!({ "status": "supported", "kind": "never" }),
        ty::Tuple(types) => json!({
            "status": "supported", "kind": "tuple",
            "elements": types.iter().map(|element| type_json(context, tcx, element)).collect::<Vec<_>>(),
        }),
        ty::Alias(_alias_kind, alias) => json!({
            "status": "supported", "kind": "alias",
            "alias_payload": alias_payload_json(tcx, alias.kind),
            "def_id": alias_def_id_json(alias.kind),
            "generic_args": generic_args_json_inner(context, tcx, alias.args),
        }),
        ty::Param(param) => json!({
            "status": "supported", "kind": "parameter",
            "index": param.index, "name": param.name.as_str(),
        }),
        ty::Bound(debruijn, bound) => json!({
            "status": "unsupported", "kind": "bound_type",
            "debruijn": format!("{debruijn:?}"), "bound": format!("{bound:?}"),
        }),
        ty::Placeholder(placeholder) => json!({
            "status": "unsupported", "kind": "placeholder_type",
            "placeholder": format!("{placeholder:?}"),
        }),
        ty::Infer(infer) => {
            json!({ "status": "unsupported", "kind": "inference_type", "inference": format!("{infer:?}") })
        }
        ty::Error(error) => {
            json!({ "status": "unsupported", "kind": "error_type", "error": format!("{error:?}") })
        }
    };
    json!({ "type_id":id, "display": ty.to_string(), "shape": shape,
        "layout": layout_json(tcx, query_ty),
        "layout_query_input_type":if query_ty == ty {Value::Null} else {type_json(context,tcx,query_ty)},
        "compiler_facts":type_compiler_facts_json(context,tcx,ty,query_ty) })
}

fn alias_payload_json(tcx: TyCtxt<'_>, kind: ty::AliasTyKind<'_>) -> Value {
    use ty::AliasTyKind as A;
    let (name, def) = match kind {
        A::Projection { def_id } => ("Projection", def_id),
        A::Inherent { def_id } => ("Inherent", def_id),
        A::Opaque { def_id } => ("Opaque", def_id),
        A::Free { def_id } => ("Free", def_id),
    };
    json!({"status":"supported","kind":name,"def_id":def_json(def),"def_path":tcx.def_path_str(def)})
}

fn alias_def_id_json(kind: ty::AliasTyKind<'_>) -> Value {
    use ty::AliasTyKind as A;
    let def = match kind {
        A::Projection { def_id }
        | A::Inherent { def_id }
        | A::Opaque { def_id }
        | A::Free { def_id } => def_id,
    };
    def_json(def)
}

fn repr_options_json(repr: &rustc_abi::ReprOptions) -> Value {
    let integer = repr.int.map(|value| match value {
        rustc_abi::IntegerType::Pointer(signed) => json!({"kind":"pointer_sized","signed":signed}),
        rustc_abi::IntegerType::Fixed(integer,signed) => json!({"kind":"fixed","integer_kind":integer.int_ty_str(),"size_bits":integer.size().bits(),"signed":signed}),
    });
    json!({
        "status":"supported",
        "integer":integer,
        "align_bytes":repr.align.map(|value|value.bytes()),
        "pack_bytes":repr.pack.map(|value|value.bytes()),
        "simd":repr.simd(),"c":repr.c(),"rust":repr.rust(),"packed":repr.packed(),
        "transparent":repr.transparent(),"linear":repr.linear(),"scalable":repr.scalable(),
        "flags_bits":repr.flags.bits(),
        "scalable_element":repr.scalable.map(|value|match value { rustc_abi::ScalableElt::ElementCount(count)=>json!({"kind":"element_count","count":count}),rustc_abi::ScalableElt::Container=>json!({"kind":"container"}) }),
        "can_randomize_type_layout":repr.can_randomize_type_layout(),
        "inhibit_enum_layout_optimization":repr.inhibit_enum_layout_opt(),
        "inhibit_struct_field_reordering":repr.inhibit_struct_field_reordering(),
        "inhibit_newtype_abi_optimization":repr.inhibit_newtype_abi_optimization(),
        "field_shuffle_seed":repr.field_shuffle_seed.as_u64()
    })
}

fn generic_args_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Value {
    generic_args_json_inner(context, tcx, args)
}

fn generic_args_json_inner<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
) -> Value {
    Value::Array(
        args.iter()
            .map(|arg| match arg.kind() {
                ty::GenericArgKind::Type(inner) => {
                    json!({ "kind": "type", "value": type_json(context, tcx, inner) })
                }
                ty::GenericArgKind::Lifetime(region) => {
                    json!({ "kind": "lifetime", "value": region_json(tcx, region) })
                }
                ty::GenericArgKind::Const(value) => {
                    json!({ "kind": "const", "value": const_type_json(context, tcx, value) })
                }
            })
            .collect(),
    )
}

fn const_type_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    value: ty::Const<'tcx>,
) -> Value {
    use ty::ConstKind as C;
    match value.kind() {
        C::Param(param) => json!({
            "status":"incomplete",
            "kind":"parameter",
            "index":param.index,
            "name":param.name.as_str(),
            "declared_type":{"status":"unknown","reason":"rustc ConstKind::Param has no declared type; resolve it through the owning generic parameter definition"},
        }),
        C::Value(constant) => json!({
            "status":"supported",
            "kind":"value",
            "type":type_json(context,tcx,constant.ty),
            "value":valtree_json(context,tcx,constant.valtree),
        }),
        C::Alias(rigidity, alias) => {
            use ty::AliasConstKind as A;
            let (kind, def_id) = match alias.kind {
                A::Projection { def_id } => ("projection", def_id),
                A::InherentSelf { def_id } => ("inherent_self", def_id),
                A::InherentImpl { def_id } => ("inherent_impl", def_id),
                A::Free { def_id } => ("free", def_id),
                A::Anon { def_id } => ("anonymous", def_id),
            };
            let rigidity = match rigidity {
                ty::IsRigid::Yes => "rigid",
                ty::IsRigid::No => "not_rigid",
            };
            json!({
                "status":"supported",
                "kind":"alias",
                "rigidity":rigidity,
                "alias_kind":kind,
                "def_id":def_json(def_id),
                "def_path":tcx.def_path_str(def_id),
                "generic_args":generic_args_json_inner(context,tcx,alias.args),
            })
        }
        C::Expr(expression) => {
            use ty::ExprKind as E;
            let (kind, operator) = match expression.kind {
                E::Binop(op) => ("binary_operator", Some(binop_name(op))),
                E::UnOp(op) => ("unary_operator", Some(unop_name(op))),
                E::FunctionCall => ("function_call", None),
                E::Cast(cast) => (
                    "cast",
                    Some(match cast {
                        ty::abstract_const::CastKind::As => "as",
                        ty::abstract_const::CastKind::Use => "use",
                    }),
                ),
            };
            json!({
                "status":"supported",
                "kind":"expression",
                "expression_kind":kind,
                "operator":operator,
                "arguments":generic_args_json_inner(context,tcx,expression.args()),
            })
        }
        C::Bound(debruijn, bound) => json!({
            "status":"unsupported",
            "kind":"bound",
            "index_kind":match debruijn {
                ty::BoundVarIndexKind::Bound(index) => json!({"kind":"bound","debruijn_index":index.as_u32()}),
                ty::BoundVarIndexKind::Canonical => json!({"kind":"canonical"}),
            },
            "variable_index":bound.var.as_u32(),
        }),
        C::Placeholder(placeholder) => json!({
            "status":"unsupported",
            "kind":"placeholder",
            "universe":placeholder.universe().as_u32(),
            "variable_index":placeholder.bound.var.as_u32(),
        }),
        C::Infer(infer) => json!({
            "status":"unsupported",
            "kind":"inference",
            "inference":match infer {
                ty::InferConst::Var(variable) => json!({"kind":"variable","index":variable.as_u32()}),
                ty::InferConst::Fresh(index) => json!({"kind":"fresh","index":index}),
            },
        }),
        C::Error(_) => json!({
            "status":"unsupported",
            "kind":"error",
        }),
    }
}

fn binop_name(operator: rustc_middle::mir::BinOp) -> &'static str {
    use rustc_middle::mir::BinOp as B;
    match operator {
        B::Add => "add",
        B::AddUnchecked => "add_unchecked",
        B::AddWithOverflow => "add_with_overflow",
        B::Sub => "sub",
        B::SubUnchecked => "sub_unchecked",
        B::SubWithOverflow => "sub_with_overflow",
        B::Mul => "mul",
        B::MulUnchecked => "mul_unchecked",
        B::MulWithOverflow => "mul_with_overflow",
        B::Div => "div",
        B::Rem => "rem",
        B::BitXor => "bit_xor",
        B::BitAnd => "bit_and",
        B::BitOr => "bit_or",
        B::Shl => "shift_left",
        B::ShlUnchecked => "shift_left_unchecked",
        B::Shr => "shift_right",
        B::ShrUnchecked => "shift_right_unchecked",
        B::Eq => "equal",
        B::Lt => "less_than",
        B::Le => "less_equal",
        B::Ne => "not_equal",
        B::Ge => "greater_equal",
        B::Gt => "greater_than",
        B::Cmp => "compare",
        B::Offset => "pointer_offset",
    }
}

fn unop_name(operator: rustc_middle::mir::UnOp) -> &'static str {
    use rustc_middle::mir::UnOp as U;
    match operator {
        U::Not => "not",
        U::Neg => "negate",
        U::PtrMetadata => "pointer_metadata",
    }
}

fn valtree_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    value: ty::ValTree<'tcx>,
) -> Value {
    match &*value {
        ty::ValTreeKind::Leaf(scalar) => json!({
            "status":"supported",
            "kind":"leaf",
            "size_bytes":scalar.size().bytes(),
            "bits_unsigned":scalar.to_bits_unchecked().to_string(),
        }),
        ty::ValTreeKind::Branch(values) => json!({
            "status":"supported",
            "kind":"branch",
            "elements":values.iter().map(|value| const_type_json(context,tcx,value)).collect::<Vec<_>>(),
        }),
    }
}

fn fn_sig_json_inner<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    sig: ty::FnSig<'tcx>,
) -> Value {
    fn_sig_json_with_query(context, tcx, sig, sig)
}

fn fn_sig_json_with_query<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    sig: ty::FnSig<'tcx>,
    query_sig: ty::FnSig<'tcx>,
) -> Value {
    json!({
        "inputs": sig.inputs().iter().zip(query_sig.inputs()).map(|(input,query)|
            type_json_with_query(context, tcx, *input, *query)).collect::<Vec<_>>(),
        "output": type_json_with_query(context, tcx, sig.output(), query_sig.output()),
        "safety": safety_json(sig.safety()),
        "abi": extern_abi_json(sig.abi()),
        "c_variadic": sig.c_variadic(),
    })
}

fn layout_json<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> Value {
    if ty.has_escaping_bound_vars() {
        return json!({
            "status":"unsupported",
            "kind":"layout",
            "reason":"type contains escaping bound variables; the pinned layout query may panic on this non-monomorphic input",
        });
    }
    if ty.has_non_region_param() {
        return json!({
            "status":"unsupported",
            "kind":"layout",
            "reason":"type still contains non-region generic parameters",
        });
    }
    if ty.has_infer() || ty.has_placeholders() {
        return json!({
            "status":"unsupported",
            "kind":"layout",
            "reason":"type still contains inference or placeholder variables",
        });
    }
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
    match tcx.layout_of(typing_env.as_query_input(ty)) {
        Ok(layout) => layout_value_json(tcx, layout),
        Err(error) => json!({
            "status": "unsupported",
            "kind": "layout_query_error",
            "rustc_debug": format!("{error:?}"),
        }),
    }
}

// Preserve queried TyAndLayout, including field-specific and uninhabited
// variant layouts which cannot be replaced by layout_of(result.ty).
fn layout_value_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    layout: rustc_abi::TyAndLayout<'tcx, ty::Ty<'tcx>>,
) -> Value {
    let field_count = layout.fields.count();
    let mut variant_data = variants_json(tcx, &layout.variants);
    if let rustc_abi::Variants::Multiple { variants, .. } = &layout.variants {
        for (index, _) in variants.iter_enumerated() {
            let variant = rustc_abi::LayoutData::for_variant(&layout, index);
            let entry = &mut variant_data["variants"][index.as_usize()];
            entry["fields"] = fields_shape_json(&variant.fields);
            entry["largest_niche"] = variant.largest_niche.map(|niche| json!({
                        "offset_bytes": niche.offset.bytes(),
                        "primitive": primitive_json(tcx, niche.value),
                        "valid_range": { "start": niche.valid_range.start.to_string(), "end": niche.valid_range.end.to_string() },
                    })).unwrap_or(Value::Null);
        }
    }
    json!({
        "status": "supported",
        "size_bytes": layout.size.bytes(),
        "abi_align_bytes": layout.align.abi.bytes(),
        "unadjusted_abi_align_bytes": layout.unadjusted_abi_align.bytes(),
        "max_repr_align_bytes": layout.max_repr_align.map(|align| align.bytes()),
        "repr_c": layout.repr_c,
        "uninhabited": layout.uninhabited,
        "fields": fields_shape_json(&layout.fields),
        "field_offsets_bytes": (0..field_count).map(|index| layout.fields.offset(index).bytes()).collect::<Vec<_>>(),
        "variants": variant_data,
        "backend_repr": backend_repr_json(tcx, layout.backend_repr),
        "largest_niche": layout.largest_niche.map(|niche| json!({
            "offset_bytes": niche.offset.bytes(),
            "primitive": primitive_json(tcx, niche.value),
            "valid_range": { "start": niche.valid_range.start.to_string(), "end": niche.valid_range.end.to_string() },
        })),
        "randomization_seed": layout.randomization_seed.as_u64(),
    })
}

fn fields_shape_json<FieldIdx: rustc_index::Idx>(
    fields: &rustc_abi::FieldsShape<FieldIdx>,
) -> Value {
    use rustc_abi::FieldsShape;
    match fields {
        FieldsShape::Primitive => json!({ "kind": "primitive", "field_count": 0 }),
        FieldsShape::Union(count) => {
            json!({ "kind": "union", "field_count": count.get(), "offset_bytes": 0 })
        }
        FieldsShape::Array { stride, count } => {
            json!({ "kind": "array", "stride_bytes": stride.bytes(), "field_count": count })
        }
        FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } => json!({
            "kind": "arbitrary",
            "field_count": offsets.len(),
            "offsets_bytes": offsets.iter().map(|offset| offset.bytes()).collect::<Vec<_>>(),
            "memory_order": in_memory_order.iter().map(|index| index.index()).collect::<Vec<_>>(),
        }),
    }
}

fn variants_json<'tcx, FieldIdx: rustc_index::Idx, VariantIdx: rustc_index::Idx>(
    tcx: TyCtxt<'tcx>,
    variants: &rustc_abi::Variants<FieldIdx, VariantIdx>,
) -> Value {
    use rustc_abi::Variants;
    match variants {
        Variants::Empty => json!({ "kind": "empty" }),
        Variants::Single { index } => json!({ "kind": "single", "variant_index": index.index() }),
        Variants::Multiple {
            tag,
            tag_encoding,
            tag_field,
            variants,
        } => json!({
            "kind": "multiple",
            "tag": scalar_json(tcx, *tag),
            "tag_encoding": tag_encoding_json(tag_encoding),
            "tag_field_index": tag_field.index(),
            "variants": variants.iter_enumerated().map(|(index, variant)| json!({
                "variant_index": index.index(),
                "size_bytes": variant.size.bytes(),
                "backend_repr": backend_repr_json(tcx, variant.backend_repr),
                "field_offsets_bytes": variant.field_offsets.iter().map(|offset| offset.bytes()).collect::<Vec<_>>(),
                "uninhabited": variant.is_uninhabited(),
            })).collect::<Vec<_>>(),
        }),
    }
}

fn tag_encoding_json<VariantIdx: rustc_index::Idx>(
    encoding: &rustc_abi::TagEncoding<VariantIdx>,
) -> Value {
    use rustc_abi::TagEncoding;
    match encoding {
        TagEncoding::Direct => json!({ "status": "supported", "kind": "direct" }),
        TagEncoding::Niche {
            untagged_variant,
            niche_variants,
            niche_start,
        } => json!({
            "status": "supported",
            "kind": "niche",
            "untagged_variant": untagged_variant.index(),
            "niche_variants": {
                "start": niche_variants.start.index(),
                "end": niche_variants.last.index(),
            },
            "niche_start": niche_start.to_string(),
        }),
    }
}

fn scalar_json(tcx: TyCtxt<'_>, scalar: rustc_abi::Scalar) -> Value {
    use rustc_abi::Scalar;
    match scalar {
        Scalar::Initialized { value, valid_range } => json!({
            "kind": "initialized",
            "primitive": primitive_json(tcx, value),
            "valid_range": { "start": valid_range.start.to_string(), "end": valid_range.end.to_string() },
        }),
        Scalar::Union { value } => {
            json!({ "kind": "union", "primitive": primitive_json(tcx, value) })
        }
    }
}

fn primitive_json(tcx: TyCtxt<'_>, primitive: rustc_abi::Primitive) -> Value {
    use rustc_abi::Primitive;
    match primitive {
        Primitive::Int(integer, signed) => json!({
            "kind": "integer", "integer_kind": integer.int_ty_str(),
            "signed": signed, "size_bytes": integer.size().bytes(),
        }),
        Primitive::Float(float) => {
            json!({ "kind": "float", "float_kind": float.ty_str(), "size_bytes": float.size().bytes() })
        }
        Primitive::Pointer(address_space) => json!({
            "kind": "pointer", "address_space": address_space.0,
            "size_bytes": primitive.size(&tcx).bytes(),
        }),
    }
}

fn backend_repr_json(tcx: TyCtxt<'_>, repr: rustc_abi::BackendRepr) -> Value {
    use rustc_abi::BackendRepr;
    match repr {
        BackendRepr::Scalar(scalar) => {
            json!({ "kind": "scalar", "scalar": scalar_json(tcx, scalar) })
        }
        BackendRepr::ScalarPair { a, b, b_offset } => json!({
            "kind": "scalar_pair", "first": scalar_json(tcx, a), "second": scalar_json(tcx, b),
            "second_offset_bytes": b_offset.bytes(),
        }),
        BackendRepr::SimdScalableVector {
            element,
            count,
            number_of_vectors,
        } => json!({
            "status":"supported", "kind": "scalable_simd_vector", "element": scalar_json(tcx, element),
            "lane_count": count.as_u64(), "vector_count": number_of_vectors.0,
        }),
        BackendRepr::SimdVector { element, count } => json!({
            "status":"supported", "kind": "simd_vector", "element": scalar_json(tcx, element), "lane_count": count.as_u64(),
        }),
        BackendRepr::Memory { sized } => json!({ "kind": "memory", "sized": sized }),
    }
}

fn statement_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    kind: &rustc_middle::mir::StatementKind<'tcx>,
) -> Value {
    use rustc_middle::mir::StatementKind as S;
    match kind {
        S::Assign(pair) => {
            json!({"status":"supported","variant":"Assign","place":place_json(context, tcx, body, &pair.0),"rvalue":rvalue_json(context, tcx, body, &pair.1)})
        }
        S::FakeRead(pair) => {
            json!({"status":"supported","variant":"FakeRead","cause":fake_read_cause_json(pair.0),"place":place_json(context, tcx, body, &pair.1)})
        }
        S::SetDiscriminant {
            place,
            variant_index,
        } => {
            json!({"status":"supported","variant":"SetDiscriminant","place":place_json(context, tcx, body, place),"variant_index":variant_index.as_u32()})
        }
        S::StorageLive(local) => {
            json!({"status":"supported","variant":"StorageLive","local":local.as_u32()})
        }
        S::StorageDead(local) => {
            json!({"status":"supported","variant":"StorageDead","local":local.as_u32()})
        }
        S::PlaceMention(place) => {
            json!({"status":"supported","variant":"PlaceMention","place":place_json(context, tcx, body, place)})
        }
        S::AscribeUserType(pair, variance) => {
            json!({"status":"supported","variant":"AscribeUserType","execution":"no_op","place":place_json(context, tcx, body, &pair.0),"user_type_projection":user_type_projection_json(&pair.1),"variance":variance_json(*variance)})
        }
        S::Coverage(value) => {
            json!({"status":"supported","variant":"Coverage","execution":"no_op","coverage":coverage_kind_json(value)})
        }
        S::Intrinsic(intrinsic) => match &**intrinsic {
            rustc_middle::mir::NonDivergingIntrinsic::Assume(value) => {
                json!({"status":"supported","variant":"Intrinsic","intrinsic":"Assume","value":operand_json(context, tcx, body, value)})
            }
            rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                json!({"status":"supported","variant":"Intrinsic","intrinsic":"CopyNonOverlapping","src":operand_json(context, tcx, body, &copy.src),"dst":operand_json(context, tcx, body, &copy.dst),"count":operand_json(context, tcx, body, &copy.count)})
            }
        },
        S::ConstEvalCounter => json!({"status":"supported","variant":"ConstEvalCounter"}),
        S::Nop => json!({"status":"supported","variant":"Nop"}),
        S::BackwardIncompatibleDropHint { place, reason } => {
            let reason = match reason {
                rustc_middle::mir::BackwardIncompatibleDropReason::Edition2024 => "edition_2024",
            };
            json!({"status":"supported","variant":"BackwardIncompatibleDropHint","place":place_json(context, tcx, body, place),"reason":{"status":"supported","kind":reason}})
        }
    }
}

fn variance_json(variance: ty::Variance) -> Value {
    use ty::Variance as V;
    let kind = match variance {
        V::Covariant => "covariant",
        V::Contravariant => "contravariant",
        V::Invariant => "invariant",
        V::Bivariant => "bivariant",
    };
    json!({"status":"supported","kind":kind})
}

fn user_type_projection_json(projection: &rustc_middle::mir::UserTypeProjection) -> Value {
    use rustc_middle::mir::ProjectionKind as P;
    let projections = projection
        .projs
        .iter()
        .map(|projection| match *projection {
            P::Deref => json!({"kind":"Deref"}),
            P::Field(index, ()) => json!({"kind":"Field","index":index.as_u32()}),
            P::Index(()) => json!({"kind":"Index"}),
            P::ConstantIndex { offset, min_length, from_end } => {
                json!({"kind":"ConstantIndex","offset":offset,"min_length":min_length,"from_end":from_end})
            }
            P::Subslice { from, to, from_end } => {
                json!({"kind":"Subslice","from":from,"to":to,"from_end":from_end})
            }
            P::Downcast(name, variant) => json!({
                "kind":"Downcast",
                "name":name.map(|name|name.as_str().to_owned()),
                "variant_index":variant.as_u32(),
            }),
            P::OpaqueCast(()) => json!({"kind":"OpaqueCast"}),
            P::UnwrapUnsafeBinder(()) => json!({"kind":"UnwrapUnsafeBinder"}),
            P::PhantomDeref => json!({"kind":"PhantomDeref"}),
        })
        .collect::<Vec<_>>();
    json!({
        "status":"supported",
        "base_index":projection.base.as_u32(),
        "projections":projections,
    })
}

fn coverage_kind_json(kind: &rustc_middle::mir::coverage::CoverageKind) -> Value {
    use rustc_middle::mir::coverage::{CoverageKind as C, PointKind};
    match kind {
        C::Point { point_kind, hir_id } => {
            let point_kind = match point_kind {
                PointKind::Expr => "expr",
                PointKind::ImplicitElse => "implicit_else",
                PointKind::FunctionEnd => "function_end",
            };
            json!({
                "status":"supported",
                "kind":"point",
                "point_kind":point_kind,
                "hir_id":{
                    "owner_def_id":def_json(hir_id.owner.def_id.to_def_id()),
                    "local_id":hir_id.local_id.as_u32(),
                },
            })
        }
        C::BlockMarker { id } => json!({
            "status":"supported",
            "kind":"block_marker",
            "id":id.as_u32(),
        }),
        C::VirtualCounter { bcb } => json!({
            "status":"supported",
            "kind":"virtual_counter",
            "bcb":bcb.as_u32(),
        }),
    }
}

fn terminator_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    kind: &rustc_middle::mir::TerminatorKind<'tcx>,
) -> Value {
    use rustc_middle::mir::TerminatorKind as T;
    match kind {
        T::Goto {
            target,
            loop_hint_attrs,
        } => {
            let hints = loop_hint_attrs
                .iter()
                .map(|hint| match hint {
                    rustc_attr_ir::UnrollAttr::Hint => json!({"kind":"Hint"}),
                    rustc_attr_ir::UnrollAttr::Full => json!({"kind":"Full"}),
                    rustc_attr_ir::UnrollAttr::Never => json!({"kind":"Never"}),
                    rustc_attr_ir::UnrollAttr::Count(count) => {
                        json!({"kind":"Count","count":count})
                    }
                })
                .collect::<Vec<_>>();
            json!({"status":"supported","variant":"Goto","target":target.as_u32(),"loop_hints":hints})
        }
        T::SwitchInt { discr, targets } => {
            json!({"status":"supported","variant":"SwitchInt","discriminant":operand_json(context, tcx, body, discr),"targets":targets.iter().map(|(value, block)| json!({"value":value.to_string(),"target":block.as_u32()})).collect::<Vec<_>>(),"otherwise":targets.otherwise().as_u32()})
        }
        T::UnwindResume => json!({"status":"supported","variant":"UnwindResume"}),
        T::UnwindTerminate(reason) => {
            json!({"status":"supported","variant":"UnwindTerminate","reason":unwind_terminate_reason_json(*reason)})
        }
        T::Return => json!({"status":"supported","variant":"Return"}),
        T::Unreachable => json!({"status":"supported","variant":"Unreachable"}),
        T::Drop {
            place,
            target,
            unwind,
            replace,
            drop,
        } => {
            let status = if drop.is_some() {
                "unsupported"
            } else {
                "supported"
            };
            json!({"status":status,"variant":"Drop","place":place_json(context, tcx, body, place),"target":target.as_u32(),"unwind":unwind_json(*unwind),"replace":replace,"async_drop":drop.map(|bb| bb.as_u32()),"unsupported_reason":drop.map(|_| "the pinned runtime interpreter requires async Drop to be expanded or reset before execution")})
        }
        T::Call {
            func,
            args,
            destination,
            target,
            unwind,
            call_source,
            fn_span,
        } => {
            json!({"status":"supported","variant":"Call","function":operand_json(context, tcx, body, func),"resolution":resolve_callee_json(context, tcx, body, func, args),"args":args.iter().map(|arg| json!({"operand":operand_json(context, tcx, body, &arg.node),"span":span_json(tcx,arg.span)})).collect::<Vec<_>>(),"destination":place_json(context, tcx, body, destination),"target":target.map(|bb| bb.as_u32()),"unwind":unwind_json(*unwind),"call_source":{"status":"supported","kind":call_source_name(*call_source)},"function_span":span_json(tcx,*fn_span)})
        }
        T::TailCall {
            func,
            args,
            fn_span,
        } => {
            json!({"status":"supported","variant":"TailCall","function":operand_json(context, tcx, body, func),"resolution":resolve_callee_json(context, tcx, body, func, args),"args":args.iter().map(|arg| json!({"operand":operand_json(context, tcx, body, &arg.node),"span":span_json(tcx,arg.span)})).collect::<Vec<_>>(),"function_span":span_json(tcx,*fn_span)})
        }
        T::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            panic_queries::register_assert(tcx, context, msg);
            json!({"status":"supported","variant":"Assert","condition":operand_json(context, tcx, body, cond),"expected":expected,"message":assert_message_json(context, tcx, body, msg),"target":target.as_u32(),"unwind":unwind_json(*unwind)})
        }
        T::Yield {
            value,
            resume,
            resume_arg,
            drop,
        } => {
            json!({"status":"supported","variant":"Yield","value":operand_json(context, tcx, body, value),"resume":resume.as_u32(),"resume_arg":place_json(context, tcx, body, resume_arg),"drop":drop.map(|bb| bb.as_u32())})
        }
        T::CoroutineDrop => json!({"status":"supported","variant":"CoroutineDrop"}),
        T::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            json!({"status":"supported","variant":"FalseEdge","real_target":real_target.as_u32(),"imaginary_target":imaginary_target.as_u32()})
        }
        T::FalseUnwind {
            real_target,
            unwind,
        } => {
            json!({"status":"supported","variant":"FalseUnwind","real_target":real_target.as_u32(),"unwind":unwind_json(*unwind)})
        }
        T::InlineAsm {
            asm_macro,
            template,
            operands,
            options,
            line_spans,
            targets,
            unwind,
        } => {
            use rustc_ast::ast::{InlineAsmOptions as O, InlineAsmTemplatePiece as P};
            use rustc_middle::mir::{InlineAsmMacro as M, InlineAsmOperand as A};
            use rustc_target::asm::{InlineAsmArch, InlineAsmRegOrRegClass as R};
            let arch = InlineAsmArch::from_arch(&tcx.sess.target.arch);
            let register = |register: R| match register {
                R::Reg(reg) => {
                    json!({"kind":"register","arch":arch.map(inline_asm_arch_name),"name":reg.name()})
                }
                R::RegClass(class) => {
                    json!({"kind":"register_class","arch":arch.map(inline_asm_arch_name),"name":class.name().as_str()})
                }
            };
            let pieces = template.iter().map(|piece| match piece {
                P::String(text) => json!({"kind":"string","text":text}),
                P::Placeholder { operand_idx, modifier, span } => json!({"kind":"placeholder","operand_index":operand_idx,"modifier":modifier.map(|c|c.to_string()),"span":span_json(tcx,*span)}),
            }).collect::<Vec<_>>();
            let operands = operands.iter().map(|operand| match operand {
                A::In { reg, value } => json!({"kind":"in","register":register(*reg),"value":operand_json(context,tcx,body,value)}),
                A::Out { reg, late, place } => json!({"kind":"out","register":register(*reg),"late":late,"place":place.as_ref().map(|p|place_json(context,tcx,body,p))}),
                A::InOut { reg, late, in_value, out_place } => json!({"kind":"inout","register":register(*reg),"late":late,"input":operand_json(context,tcx,body,in_value),"output":out_place.as_ref().map(|p|place_json(context,tcx,body,p))}),
                A::Const { value } => json!({"kind":"const","value":const_operand_json(context,tcx,body,value)}),
                A::SymFn { value } => json!({"kind":"sym_fn","value":const_operand_json(context,tcx,body,value)}),
                A::SymStatic { def_id } => json!({"kind":"sym_static","def_id":def_json(*def_id)}),
                A::Label { target_index } => json!({"kind":"label","target_index":target_index}),
            }).collect::<Vec<_>>();
            json!({"status":"supported","variant":"InlineAsm","asm_macro":match asm_macro { M::Asm => "asm", M::NakedAsm => "naked_asm" },
                "template":pieces,"operands":operands,
                "options":{"pure":options.contains(O::PURE),"nomem":options.contains(O::NOMEM),"readonly":options.contains(O::READONLY),"preserves_flags":options.contains(O::PRESERVES_FLAGS),"noreturn":options.contains(O::NORETURN),"nostack":options.contains(O::NOSTACK),"att_syntax":options.contains(O::ATT_SYNTAX),"raw":options.contains(O::RAW),"may_unwind":options.contains(O::MAY_UNWIND)},
                "line_spans":line_spans.iter().map(|span|span_json(tcx,*span)).collect::<Vec<_>>(),
                "targets":targets.iter().map(|bb|bb.as_u32()).collect::<Vec<_>>(),"unwind":unwind_json(*unwind),
                "execution_obligation":"target-specific assembly execution is not supplied by syntax lowering"})
        }
    }
}

fn inline_asm_arch_name(arch: rustc_target::asm::InlineAsmArch) -> &'static str {
    use rustc_target::asm::InlineAsmArch as A;
    match arch {
        A::X86 => "X86",
        A::X86_64 => "X86_64",
        A::Arm => "Arm",
        A::Arm64EC => "Arm64EC",
        A::AArch64 => "AArch64",
        A::Amdgpu => "Amdgpu",
        A::RiscV32 => "RiscV32",
        A::RiscV64 => "RiscV64",
        A::Nvptx64 => "Nvptx64",
        A::PowerPC => "PowerPC",
        A::PowerPC64 => "PowerPC64",
        A::Hexagon => "Hexagon",
        A::LoongArch32 => "LoongArch32",
        A::LoongArch64 => "LoongArch64",
        A::Mips => "Mips",
        A::Mips64 => "Mips64",
        A::Xtensa => "Xtensa",
        A::S390x => "S390x",
        A::Sparc => "Sparc",
        A::Sparc64 => "Sparc64",
        A::SpirV => "SpirV",
        A::Wasm32 => "Wasm32",
        A::Wasm64 => "Wasm64",
        A::Bpf => "Bpf",
        A::Avr => "Avr",
        A::Msp430 => "Msp430",
        A::M68k => "M68k",
        A::CSKY => "CSKY",
    }
}

fn place_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
) -> Value {
    use rustc_middle::mir::ProjectionElem as P;
    let projection = place.iter_projections().map(|(base, elem)| {
        let projected_place = base.project_deeper(&[elem], tcx);
        let projected_type = type_json(context, tcx, projected_place.ty(body, tcx).ty);
        let mut node = match elem {
            P::Deref => json!({"kind":"Deref"}),
            P::Field(index, ty) => json!({"kind":"Field","index":index.as_u32(),"field_type":type_json(context, tcx,ty)}),
            P::Index(local) => json!({"kind":"Index","local":local.as_u32()}),
            P::ConstantIndex { offset, min_length, from_end } => json!({"kind":"ConstantIndex","offset":offset,"min_length":min_length,"from_end":from_end}),
            P::Subslice { from, to, from_end } => json!({"kind":"Subslice","from":from,"to":to,"from_end":from_end}),
            P::Downcast(name, variant) => json!({"kind":"Downcast","name":name.map(|n|n.as_str().to_owned()),"variant_index":variant.as_u32()}),
            P::OpaqueCast(ty) => json!({"kind":"OpaqueCast","cast_type":type_json(context, tcx,ty)}),
            P::UnwrapUnsafeBinder(ty) => json!({"kind":"UnwrapUnsafeBinder","inner_type":type_json(context, tcx,ty)}),
            P::PhantomDeref => json!({"kind":"PhantomDeref"}),
        };
        if let Some(fields) = node.as_object_mut() {
            fields.insert("resulting_type".into(), projected_type);
        }
        node
    }).collect::<Vec<_>>();
    let place_ty = place.ty(body, tcx).ty;
    json!({"status":"supported","local":place.local.as_u32(),"projection":projection,"type":type_json(context, tcx,place_ty)})
}

fn operand_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &rustc_middle::mir::Operand<'tcx>,
) -> Value {
    use rustc_middle::mir::Operand as O;
    match operand {
        O::Copy(place) => {
            json!({"status":"supported","kind":"Copy","place":place_json(context, tcx,body,place)})
        }
        O::Move(place) => {
            json!({"status":"supported","kind":"Move","place":place_json(context, tcx,body,place)})
        }
        O::Constant(value) => {
            json!({"status":"supported","kind":"Constant","constant":const_operand_json(context, tcx,body,value)})
        }
        O::RuntimeChecks(check) => {
            json!({"status":"supported","kind":"RuntimeChecks","check":runtime_check_json(tcx,*check)})
        }
    }
}

fn vtable_allocation_for_unsize<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    source: &rustc_middle::mir::Operand<'tcx>,
    target_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Value> {
    let source_ty = source.ty(body, tcx);
    let source_pointee = match *source_ty.kind() {
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => pointee,
        _ => source_ty,
    };
    let target_pointee = match *target_ty.kind() {
        ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => pointee,
        _ => target_ty,
    };
    if source_pointee.has_non_region_param()
        || source_pointee.has_escaping_bound_vars()
        || target_pointee.has_non_region_param()
        || target_pointee.has_escaping_bound_vars()
    {
        return Some(json!({
            "status":"unknown",
            "kind":"vtable_requires_concrete_types",
            "source_type":type_json(context,tcx,source_pointee),
            "target_type":type_json(context,tcx,target_pointee),
            "reason":"rustc cannot provide a concrete symbolic vtable for generic or bound-variable pointee types",
        }));
    }
    let (source_tail, target_tail) =
        tcx.struct_lockstep_tails_for_codegen(source_pointee, target_pointee, body.typing_env(tcx));
    let ty::Dynamic(predicates, _) = target_tail.kind() else {
        return None;
    };
    match source_tail.kind() {
        ty::Dynamic(source_predicates, _) if source_predicates == predicates => Some(json!({
            "status":"supported",
            "kind":"same_dynamic_vtable_noop",
            "type":type_json(context,tcx,source_tail),
        })),
        ty::Dynamic(..) => {
            // Miri does not construct a fresh vtable for a dyn-to-dyn upcast.
            // It reads the source vtable from the operand, asks the exact
            // compiler `supertrait_vtable_slot((source, target))` query, then
            // checks the TraitVPtr/prefix against that runtime table. The
            // query is emitted by cast_queries for this same lockstep pair;
            // concrete receiver/vtable identity intentionally remains runtime
            // evidence and is not fabricated here.
            Some(json!({
                "status":"supported",
                "kind":"dynamic_vtable_upcast",
                "source_type":type_json(context,tcx,source_ty),
                "target_type":type_json(context,tcx,target_ty),
                "source_pointee_type":type_json(context,tcx,source_pointee),
                "target_pointee_type":type_json(context,tcx,target_pointee),
                "source_tail_type":type_json(context,tcx,source_tail),
                "target_tail_type":type_json(context,tcx,target_tail),
                "supertrait_slot_query":{
                    "status":"supported",
                    "query_kind":"supertrait_slot",
                    "typing_env":"fully_monomorphized",
                    "input_source":type_json(context,tcx,source_tail),
                    "input_target":type_json(context,tcx,target_tail),
                },
                "runtime_vtable":"source_operand_metadata",
            }))
        }
        _ => {
            context
                .vtable_query_requests
                .insert((source_tail, predicates));
            let input_type_id = context.type_id(source_tail);
            let input_predicate_ids = predicates
                .iter()
                .map(|predicate| context.predicate_id(predicate))
                .collect::<Vec<_>>();
            let input_predicates = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Vec<_>>();
            Some(json!({
                "status":"supported",
                "kind":"symbolic_vtable_allocation",
                "vtable_query":{"status":"supported","source_type":type_json(context,tcx,source_ty),
                    "target_type":type_json(context,tcx,target_ty),
                    "source_pointee_type":type_json(context,tcx,source_pointee),
                    "target_pointee_type":type_json(context,tcx,target_pointee),
                    "input_type":type_json(context,tcx,source_tail),
                    "input_predicates":input_predicates,
                    "source_tail_type":type_json(context,tcx,source_tail),
                    "target_tail_type":type_json(context,tcx,target_tail),
                    "_query_key":{"input_type_id":input_type_id,"input_predicate_ids":input_predicate_ids}},
                "vtable_probe":{"status":"incomplete","kind":"symbolic_vtable_allocation",
                    "salt_policy":"exporter uses CTFE_ALLOC_SALT; Miri runtime allocation salts may be randomized; probe is diagnostic only and carries no allocation identity"},
            }))
        }
    }
}

fn rvalue_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
) -> Value {
    use rustc_middle::mir::Rvalue as R;
    match rvalue {
        R::Use(value, retag) => {
            json!({"status":"supported","kind":"Use","operand":operand_json(context, tcx,body,value),"retag":{"status":"supported","kind":if retag.yes() { "yes" } else { "no" },"performs_retag":retag.yes()}})
        }
        R::Repeat(value, count) => {
            json!({"status":"supported","kind":"Repeat","operand":operand_json(context, tcx,body,value),"count":const_type_json(context,tcx,*count)})
        }
        R::Ref(region, kind, place) => {
            json!({"status":"supported","kind":"Ref","region":region_json(tcx,*region),"borrow_kind":borrow_kind_json(*kind),"place":place_json(context, tcx,body,place)})
        }
        R::ThreadLocalRef(def) => {
            let initializer = if tcx.is_foreign_item(*def) {
                json!({"status":"unsupported","reason":"foreign thread-local initializer is unavailable"})
            } else {
                match tcx.eval_static_initializer(*def) {
                    Ok(value) => json!({
                        "status":"supported",
                        "allocation":allocation_memory_payload(context,tcx,value.inner()),
                    }),
                    Err(error) => json!({
                        "status":"unsupported",
                        "error_debug":format!("{error:?}"),
                    }),
                }
            };
            json!({
                "status":"supported",
                "kind":"ThreadLocalRef",
                "global_info":static_global_info_json(tcx,*def),
                "def_id":def_json(*def),
                "def_path":tcx.def_path_str(*def),
                "initializer":initializer,
            })
        }
        R::RawPtr(kind, place) => {
            let pointer_kind = match kind {
                rustc_middle::mir::RawPtrKind::Mut => "mutable",
                rustc_middle::mir::RawPtrKind::Const => "constant",
                rustc_middle::mir::RawPtrKind::FakeForPtrMetadata => "metadata_only",
            };
            json!({"status":"supported","kind":"RawPtr","pointer_kind":{"kind":pointer_kind},"place":place_json(context, tcx,body,place)})
        }
        R::Cast(kind, value, target) => {
            if matches!(
                kind,
                rustc_middle::mir::CastKind::Transmute
                    | rustc_middle::mir::CastKind::Subtype
                    | rustc_middle::mir::CastKind::BoxDerefTransmute
            ) {
                context
                    .covariance_query_requests
                    .insert((value.ty(body, tcx), *target));
            }
            if matches!(
                kind,
                rustc_middle::mir::CastKind::PointerCoercion(
                    ty::adjustment::PointerCoercion::Unsize,
                    _
                )
            ) {
                let source = value.ty(body, tcx);
                context.cast_unsize_requests.insert((source, *target));
                if let (Some(a), Some(b)) = (source.builtin_deref(true), target.builtin_deref(true))
                {
                    context.cast_unsize_requests.insert((a, b));
                }
            }
            if matches!(kind, rustc_middle::mir::CastKind::BoxDerefTransmute) {
                if let Some(pointee) = target.builtin_deref(true) {
                    context.cast_box_requests.insert(pointee);
                }
            }
            let vtable = if matches!(
                kind,
                rustc_middle::mir::CastKind::PointerCoercion(
                    rustc_middle::ty::adjustment::PointerCoercion::Unsize,
                    _,
                )
            ) {
                vtable_allocation_for_unsize(context, tcx, body, value, *target)
            } else {
                None
            };
            let status = vtable
                .as_ref()
                .and_then(|value| value.get("status"))
                .and_then(Value::as_str)
                .unwrap_or("supported");
            let vtable_query = vtable
                .as_ref()
                .and_then(|value| value.get("vtable_query"))
                .cloned();
            let vtable_probe = vtable
                .as_ref()
                .and_then(|value| value.get("vtable_probe"))
                .cloned();
            let vtable_allocation = if vtable_query.is_some() {
                Value::Null
            } else {
                vtable.clone().unwrap_or(Value::Null)
            };
            json!({"status":status,"kind":"Cast","cast_kind":cast_kind_json(*kind),"operand":operand_json(context, tcx,body,value),"target_type":type_json(context, tcx,*target),"vtable_allocation":vtable_allocation,"vtable_query":vtable_query,"vtable_probe":vtable_probe})
        }
        R::BinaryOp(op, pair) => {
            json!({"status":"supported","kind":"BinaryOp","operator":{"status":"supported","kind":binop_name(*op)},"left":operand_json(context, tcx,body,&pair.0),"right":operand_json(context, tcx,body,&pair.1)})
        }
        R::UnaryOp(op, value) => {
            json!({"status":"supported","kind":"UnaryOp","operator":{"status":"supported","kind":unop_name(*op)},"operand":operand_json(context, tcx,body,value)})
        }
        R::Discriminant(place) => {
            json!({"status":"supported","kind":"Discriminant","place":place_json(context, tcx,body,place)})
        }
        R::Aggregate(kind, values) => {
            json!({"status":"supported","kind":"Aggregate","aggregate_kind":aggregate_kind_json(context, tcx,kind),"operands":values.iter().map(|value|operand_json(context, tcx,body,value)).collect::<Vec<_>>()})
        }
        R::CopyForDeref(place) => {
            json!({"status":"supported","kind":"CopyForDeref","place":place_json(context, tcx,body,place)})
        }
        R::WrapUnsafeBinder(value, ty) => {
            json!({"status":"supported","kind":"WrapUnsafeBinder","operand":operand_json(context, tcx,body,value),"type":type_json(context, tcx,*ty)})
        }
        R::Reborrow(ty, mutability, place) => {
            json!({"status":"supported","kind":"Reborrow","type":type_json(context, tcx,*ty),"mutability":mutability_json(*mutability),"place":place_json(context, tcx,body,place)})
        }
    }
}

fn borrow_kind_json(kind: rustc_middle::mir::BorrowKind) -> Value {
    use rustc_middle::mir::BorrowKind as B;
    match kind {
        B::Shared => json!({"status":"supported","kind":"shared"}),
        B::Fake(fake) => {
            let fake_kind = match fake {
                rustc_middle::mir::FakeBorrowKind::Shallow => "shallow",
                rustc_middle::mir::FakeBorrowKind::Deep => "deep",
            };
            json!({"status":"supported","kind":"fake","fake_kind":fake_kind,"retag_mode":"default"})
        }
        B::Mut { kind } => {
            let mut_kind = match kind {
                rustc_middle::mir::MutBorrowKind::Default => "default",
                rustc_middle::mir::MutBorrowKind::TwoPhaseBorrow => "two_phase",
                rustc_middle::mir::MutBorrowKind::ClosureCapture => "closure_capture",
            };
            json!({"status":"supported","kind":"mutable","mutability_kind":mut_kind})
        }
    }
}

fn safety_json(safety: rustc_hir::Safety) -> Value {
    match safety {
        rustc_hir::Safety::Safe => json!({"status":"supported","kind":"safe"}),
        rustc_hir::Safety::Unsafe => json!({"status":"supported","kind":"unsafe"}),
    }
}

fn mutability_json(mutability: rustc_ast::Mutability) -> Value {
    match mutability {
        rustc_ast::Mutability::Mut => json!({"status":"supported","kind":"mutable"}),
        rustc_ast::Mutability::Not => json!({"status":"supported","kind":"immutable"}),
    }
}

fn extern_abi_json(abi: rustc_abi::ExternAbi) -> Value {
    use rustc_abi::ExternAbi as A;
    let (kind, unwind) = match abi {
        A::C { unwind } => ("c", Some(unwind)),
        A::System { unwind } => ("system", Some(unwind)),
        A::Rust => ("rust", None),
        A::RustCall => ("rust_call", None),
        A::RustCold => ("rust_cold", None),
        A::RustInvalid => ("rust_invalid", None),
        A::RustPreserveNone => ("rust_preserve_none", None),
        A::RustTail => ("rust_tail", None),
        A::LlvmIntrinsic => ("llvm_intrinsic", None),
        A::Custom => ("custom", None),
        A::EfiApi => ("efi_api", None),
        A::Swift => ("swift", None),
        A::Aapcs { unwind } => ("aapcs", Some(unwind)),
        A::CmseNonSecureCall => ("cmse_nonsecure_call", None),
        A::CmseNonSecureEntry => ("cmse_nonsecure_entry", None),
        A::GpuKernel => ("gpu_kernel", None),
        A::PtxKernel => ("ptx_kernel", None),
        A::AvrInterrupt => ("avr_interrupt", None),
        A::AvrNonBlockingInterrupt => ("avr_non_blocking_interrupt", None),
        A::Msp430Interrupt => ("msp430_interrupt", None),
        A::RiscvInterruptM => ("riscv_interrupt_machine", None),
        A::RiscvInterruptS => ("riscv_interrupt_supervisor", None),
        A::X86Interrupt => ("x86_interrupt", None),
        A::Cdecl { unwind } => ("cdecl", Some(unwind)),
        A::Stdcall { unwind } => ("stdcall", Some(unwind)),
        A::Fastcall { unwind } => ("fastcall", Some(unwind)),
        A::Thiscall { unwind } => ("thiscall", Some(unwind)),
        A::Vectorcall { unwind } => ("vectorcall", Some(unwind)),
        A::SysV64 { unwind } => ("sysv64", Some(unwind)),
        A::Win64 { unwind } => ("win64", Some(unwind)),
    };
    json!({"status":"supported","kind":kind,"unwind":unwind,"source_spelling":abi.as_str()})
}

fn canon_abi_json(abi: rustc_abi::CanonAbi) -> Value {
    use rustc_abi::CanonAbi as A;
    match abi {
        A::C => json!({"status":"supported","kind":"c"}),
        A::Rust => json!({"status":"supported","kind":"rust"}),
        A::RustCold => json!({"status":"supported","kind":"rust_cold"}),
        A::RustPreserveNone => json!({"status":"supported","kind":"rust_preserve_none"}),
        A::RustTail => json!({"status":"supported","kind":"rust_tail"}),
        A::Custom => json!({"status":"supported","kind":"custom"}),
        A::Swift => json!({"status":"supported","kind":"swift"}),
        A::Arm(call) => json!({"status":"supported","kind":"arm","arm_call":match call {
            rustc_abi::ArmCall::Aapcs => "aapcs",
            rustc_abi::ArmCall::CCmseNonSecureCall => "cmse_nonsecure_call",
            rustc_abi::ArmCall::CCmseNonSecureEntry => "cmse_nonsecure_entry",
        }}),
        A::GpuKernel => json!({"status":"supported","kind":"gpu_kernel"}),
        A::Interrupt(kind) => {
            json!({"status":"supported","kind":"interrupt","interrupt_kind":match kind {
                rustc_abi::InterruptKind::Avr => "avr",
                rustc_abi::InterruptKind::AvrNonBlocking => "avr_non_blocking",
                rustc_abi::InterruptKind::Msp430 => "msp430",
                rustc_abi::InterruptKind::RiscvMachine => "riscv_machine",
                rustc_abi::InterruptKind::RiscvSupervisor => "riscv_supervisor",
                rustc_abi::InterruptKind::X86 => "x86",
            }})
        }
        A::X86(call) => json!({"status":"supported","kind":"x86","x86_call":match call {
            rustc_abi::X86Call::Fastcall => "fastcall",
            rustc_abi::X86Call::Stdcall => "stdcall",
            rustc_abi::X86Call::SysV64 => "sysv64",
            rustc_abi::X86Call::Thiscall => "thiscall",
            rustc_abi::X86Call::Vectorcall => "vectorcall",
            rustc_abi::X86Call::Win64 => "win64",
        }}),
    }
}

fn arg_extension_json(extension: rustc_target::callconv::ArgExtension) -> Value {
    use rustc_target::callconv::ArgExtension as E;
    let kind = match extension {
        E::None => "none",
        E::Zext => "zero_extend",
        E::Sext => "sign_extend",
    };
    json!({"status":"supported","kind":kind})
}

fn indirect_mode_json(mode: rustc_target::callconv::IndirectMode) -> Value {
    use rustc_target::callconv::IndirectMode as M;
    let kind = match mode {
        M::Pointer => "pointer",
        M::OnStack => "on_stack",
        M::AmdgpuKernelArg => "amdgpu_kernel_argument",
    };
    json!({"status":"supported","kind":kind})
}

fn unwind_terminate_reason_json(reason: rustc_middle::mir::UnwindTerminateReason) -> Value {
    use rustc_middle::mir::UnwindTerminateReason as R;
    let kind = match reason {
        R::Abi => "abi",
        R::InCleanup => "in_cleanup",
    };
    json!({"status":"supported","kind":kind})
}

fn cast_kind_json(kind: rustc_middle::mir::CastKind) -> Value {
    use rustc_middle::mir::CastKind as C;
    use rustc_middle::ty::adjustment::PointerCoercion as P;
    match kind {
        C::PointerExposeProvenance => {
            json!({"status":"supported","kind":"PointerExposeProvenance"})
        }
        C::PointerWithExposedProvenance => {
            json!({"status":"supported","kind":"PointerWithExposedProvenance"})
        }
        C::PointerCoercion(coercion, source) => {
            let coercion = match coercion {
                P::ReifyFnPointer(safety) => {
                    json!({"kind":"ReifyFnPointer","safety":safety_json(safety)})
                }
                P::UnsafeFnPointer => json!({"kind":"UnsafeFnPointer"}),
                P::ClosureFnPointer(safety) => {
                    json!({"kind":"ClosureFnPointer","safety":safety_json(safety)})
                }
                P::MutToConstPointer => json!({"kind":"MutToConstPointer"}),
                P::ArrayToPointer => json!({"kind":"ArrayToPointer"}),
                P::Unsize => json!({"kind":"Unsize"}),
            };
            let source = match source {
                rustc_middle::mir::CoercionSource::AsCast => "as_cast",
                rustc_middle::mir::CoercionSource::Implicit => "implicit",
            };
            json!({"status":"supported","kind":"PointerCoercion","coercion":coercion,"source":{"kind":source}})
        }
        C::IntToInt => json!({"status":"supported","kind":"IntToInt"}),
        C::FloatToInt => json!({"status":"supported","kind":"FloatToInt"}),
        C::FloatToFloat => json!({"status":"supported","kind":"FloatToFloat"}),
        C::IntToFloat => json!({"status":"supported","kind":"IntToFloat"}),
        C::PtrToPtr => json!({"status":"supported","kind":"PtrToPtr"}),
        C::FnPtrToPtr => json!({"status":"supported","kind":"FnPtrToPtr"}),
        C::Transmute => json!({"status":"supported","kind":"Transmute"}),
        C::BoxDerefTransmute => json!({"status":"supported","kind":"BoxDerefTransmute"}),
        C::Subtype => json!({"status":"supported","kind":"Subtype"}),
    }
}

fn aggregate_kind_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    kind: &rustc_middle::mir::AggregateKind<'tcx>,
) -> Value {
    use rustc_middle::mir::AggregateKind as A;
    match kind {
        A::Array(ty) => json!({"kind":"Array","element_type":type_json(context, tcx,*ty)}),
        A::Tuple => json!({"kind":"Tuple"}),
        A::Adt(def, variant, args, user_ty, active_field) => {
            json!({"kind":"Adt","def_id":def_json(*def),"def_path":tcx.def_path_str(*def),"variant_index":variant.as_u32(),"generic_args":generic_args_json(context, tcx,*args),"user_type_annotation":user_ty.map(|value|json!({"kind":"annotation_ref","index":value.as_u32()})),"active_union_field":active_field.map(|field|field.as_u32())})
        }
        A::Closure(def, args) => {
            json!({"kind":"Closure","def_id":def_json(*def),"def_path":tcx.def_path_str(*def),"generic_args":generic_args_json(context, tcx,*args)})
        }
        A::Coroutine(def, args) => {
            json!({"kind":"Coroutine","def_id":def_json(*def),"def_path":tcx.def_path_str(*def),"generic_args":generic_args_json(context, tcx,*args)})
        }
        A::CoroutineClosure(def, args) => {
            json!({"kind":"CoroutineClosure","def_id":def_json(*def),"def_path":tcx.def_path_str(*def),"generic_args":generic_args_json(context, tcx,*args)})
        }
        A::RawPtr(ty, mutability) => {
            json!({"kind":"RawPtr","pointee_type":type_json(context, tcx,*ty),"mutability":mutability_json(*mutability)})
        }
    }
}

fn assert_message_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    message: &rustc_middle::mir::AssertMessage<'tcx>,
) -> Value {
    use rustc_middle::mir::AssertKind as A;
    match message {
        A::BoundsCheck { len, index } => {
            json!({"kind":"BoundsCheck","length":operand_json(context, tcx,body,len),"index":operand_json(context, tcx,body,index)})
        }
        A::Overflow(op, left, right) => {
            json!({"kind":"Overflow","operator":{"status":"supported","kind":binop_name(*op)},"left":operand_json(context, tcx,body,left),"right":operand_json(context, tcx,body,right)})
        }
        A::OverflowNeg(value) => {
            json!({"kind":"OverflowNeg","operand":operand_json(context, tcx,body,value)})
        }
        A::DivisionByZero(value) => {
            json!({"kind":"DivisionByZero","operand":operand_json(context, tcx,body,value)})
        }
        A::RemainderByZero(value) => {
            json!({"kind":"RemainderByZero","operand":operand_json(context, tcx,body,value)})
        }
        A::ResumedAfterReturn(kind) => {
            json!({"kind":"ResumedAfterReturn","coroutine_kind":coroutine_kind_json(*kind)})
        }
        A::ResumedAfterPanic(kind) => {
            json!({"kind":"ResumedAfterPanic","coroutine_kind":coroutine_kind_json(*kind)})
        }
        A::ResumedAfterDrop(kind) => {
            json!({"kind":"ResumedAfterDrop","coroutine_kind":coroutine_kind_json(*kind)})
        }
        A::MisalignedPointerDereference { required, found } => {
            json!({"kind":"MisalignedPointerDereference","required":operand_json(context, tcx,body,required),"found":operand_json(context, tcx,body,found)})
        }
        A::NullPointerDereference => json!({"kind":"NullPointerDereference"}),
        A::NullReferenceConstructed => json!({"kind":"NullReferenceConstructed"}),
        A::InvalidEnumConstruction(value) => {
            json!({"kind":"InvalidEnumConstruction","operand":operand_json(context, tcx,body,value)})
        }
    }
}

fn unwind_json(unwind: rustc_middle::mir::UnwindAction) -> Value {
    use rustc_middle::mir::UnwindAction as U;
    match unwind {
        U::Continue => json!({"kind":"Continue"}),
        U::Unreachable => json!({"kind":"Unreachable"}),
        U::Terminate(reason) => {
            json!({"kind":"Terminate","reason":unwind_terminate_reason_json(reason)})
        }
        U::Cleanup(block) => json!({"kind":"Cleanup","target":block.as_u32()}),
    }
}

fn def_json(def: rustc_hir::def_id::DefId) -> Value {
    json!({"crate":def.krate.as_u32(),"index":def.index.as_u32()})
}

fn instance_kind_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    kind: ty::InstanceKind<'tcx>,
) -> Value {
    use ty::{InstanceKind as I, ShimKind as S};
    match kind {
        I::Item(def) => json!({"kind":"item","def_id":def_json(def)}),
        I::Intrinsic(def) => json!({"kind":"intrinsic","def_id":def_json(def)}),
        I::LlvmIntrinsic(def) => json!({"kind":"llvm_intrinsic","def_id":def_json(def)}),
        I::Virtual(def, slot) => {
            json!({"kind":"virtual","def_id":def_json(def),"dispatch_slot":slot})
        }
        I::Shim(shim) => match shim {
            S::VTable(def) => json!({"kind":"shim","shim_kind":"vtable","def_id":def_json(def)}),
            S::Reify(def, reason) => json!({
                "kind":"shim","shim_kind":"reify","def_id":def_json(def),
                "reason":reason.map(|reason| match reason {
                    ty::ReifyReason::FnPtr => "function_pointer",
                    ty::ReifyReason::Vtable => "vtable",
                }),
            }),
            S::FnPtr(def, fn_ty) => {
                json!({"kind":"shim","shim_kind":"fn_pointer","def_id":def_json(def),"function_type":type_json(context,tcx,fn_ty)})
            }
            S::ClosureOnce {
                call_once,
                closure,
                track_caller,
            } => json!({
                "kind":"shim","shim_kind":"closure_once","call_once_def_id":def_json(call_once),
                "closure_def_id":def_json(closure),"track_caller":track_caller,
            }),
            S::ConstructCoroutineInClosure {
                coroutine_closure_def_id,
                receiver_by_ref,
            } => json!({
                "kind":"shim","shim_kind":"construct_coroutine_in_closure",
                "coroutine_closure_def_id":def_json(coroutine_closure_def_id),
                "receiver_by_ref":receiver_by_ref,
            }),
            S::ThreadLocal(def) => {
                json!({"kind":"shim","shim_kind":"thread_local","def_id":def_json(def)})
            }
            S::FutureDropPoll(def, proxy_ty, implementation_ty) => json!({
                "kind":"shim","shim_kind":"future_drop_poll","def_id":def_json(def),
                "proxy_coroutine_type":type_json(context,tcx,proxy_ty),
                "implementation_coroutine_type":type_json(context,tcx,implementation_ty),
            }),
            S::DropGlue(def, drop_ty) => json!({
                "kind":"shim","shim_kind":"drop_glue","def_id":def_json(def),
                "drop_type":drop_ty.map(|ty|type_json(context,tcx,ty)),
            }),
            S::Clone(def, clone_ty) => json!({
                "kind":"shim","shim_kind":"clone","def_id":def_json(def),
                "clone_type":type_json(context,tcx,clone_ty),
            }),
            S::FnPtrAsPtr(def, fn_ty) => {
                json!({"kind":"shim","shim_kind":"fn_pointer_as_pointer","def_id":def_json(def),"function_type":type_json(context,tcx,fn_ty)})
            }
            S::FnPtrFromPtr(def, fn_ty) => {
                json!({"kind":"shim","shim_kind":"fn_pointer_from_pointer","def_id":def_json(def),"function_type":type_json(context,tcx,fn_ty)})
            }
            S::AsyncDropGlueCtor(def, drop_ty) => {
                json!({"kind":"shim","shim_kind":"async_drop_glue_constructor","def_id":def_json(def),"drop_type":type_json(context,tcx,drop_ty)})
            }
            S::AsyncDropGlue(def, coroutine_ty) => {
                json!({"kind":"shim","shim_kind":"async_drop_glue","def_id":def_json(def),"coroutine_type":type_json(context,tcx,coroutine_ty)})
            }
        },
    }
}

fn resolve_callee_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
) -> Value {
    let func_ty = func.ty(body, tcx);
    match *func_ty.kind() {
        ty::FnDef(def, args) => {
            match ty::Instance::try_resolve(tcx, body.typing_env(tcx), def, args.skip_binder()) {
                Ok(Some(instance)) => {
                    let instance_id = context.register_instance(instance);
                    // step.rs derives extra arguments from the normalized original
                    // function signature, not the callee's ABI argument count.
                    let signature = tcx.try_normalize_erasing_regions(
                        body.typing_env(tcx),
                        ty::Unnormalized::new_wip(func_ty.fn_sig(tcx)),
                    );
                    if let Ok(signature) = signature {
                        let signature = tcx.instantiate_bound_regions_with_erased(signature);
                        if let Some(extra) = call_args.get(signature.inputs().len()..) {
                            let extra = tcx.mk_type_list_from_iter(
                                extra.iter().map(|arg| arg.node.ty(body, tcx)),
                            );
                            context.instance_abi_requests.insert((instance, extra));
                        }
                    }
                    let abi = tcx.fn_abi_of_instance(
                        body.typing_env(tcx)
                            .as_query_input((instance, ty::List::empty())),
                    );
                    match abi {
                        Ok(abi) => {
                            let (status, kind, dispatch_slot) = match instance.def {
                                ty::InstanceKind::Virtual(_, slot) => {
                                    ("supported", "virtual_dispatch", Some(slot))
                                }
                                _ => ("supported", "resolved_instance", None),
                            };
                            let virtual_resolution =
                                if let ty::InstanceKind::Virtual(def, slot) = instance.def {
                                    json!({"status":"supported","instance_id":instance_id,
                                    "method_definition":def_json(def),"dispatch_slot":slot,
                                    "generic_args":generic_args_json(context,tcx,instance.args),
                                    "candidate_query_ids":[],
                                    "selection":"deferred to the runtime receiver vtable"})
                                } else {
                                    Value::Null
                                };
                            json!({"status":status,"kind":kind,"function_type":type_json(context,tcx,func_ty),"instance_id":instance_id,"dispatch_slot":dispatch_slot,"instance_kind":instance_kind_json(context,tcx,instance.def),"instance_def_path":tcx.def_path_str(instance.def.def_id()),"generic_args":generic_args_json(context, tcx,instance.args),"fn_abi":fn_abi_json(context, tcx,abi),"virtual_resolution":virtual_resolution})
                        }
                        Err(error) => {
                            json!({"status":"unsupported","kind":"resolved_instance_abi_error","instance_id":instance_id,"error":format!("{error:?}")})
                        }
                    }
                }
                Ok(None) => {
                    json!({"status":"unknown","kind":"unresolved_or_intrinsic_fn_def","function_type":type_json(context,tcx,func_ty)})
                }
                Err(error) => {
                    json!({"status":"unsupported","kind":"instance_resolution_error","error":format!("{error:?}")})
                }
            }
        }
        ty::FnPtr(..) => {
            if func_ty.has_non_region_param()
                || func_ty.has_escaping_bound_vars()
                || func_ty.has_infer()
                || func_ty.has_placeholders()
            {
                return unavailable_compiler_fact(
                    "indirect function pointer still requires caller instantiation",
                );
            }
            let environment = body.typing_env(tcx);
            match tcx.try_normalize_erasing_regions(
                environment,
                ty::Unnormalized::new_wip(func_ty.fn_sig(tcx)),
            ) {
                Ok(signature) => {
                    let signature = tcx.instantiate_bound_regions_with_erased(signature);
                    match call_args.get(signature.inputs().len()..) {
                        Some(extra) => {
                            let extra = tcx.mk_type_list_from_iter(
                                extra.iter().map(|arg| arg.node.ty(body, tcx)),
                            );
                            context.fn_pointer_abi_requests.insert((func_ty, extra));
                            if extra.has_non_region_param()
                                || extra.has_escaping_bound_vars()
                                || extra.has_infer()
                                || extra.has_placeholders()
                            {
                                return unavailable_compiler_fact(
                                    "indirect extra argument types still require caller instantiation",
                                );
                            }
                            match tcx.fn_abi_of_fn_ptr(
                                environment.as_query_input((func_ty.fn_sig(tcx), extra)),
                            ) {
                                Ok(abi) => {
                                    json!({"status":"supported","kind":"indirect_function_pointer",
                                    "function_type":type_json(context,tcx,func_ty),"signature":fn_sig_json_inner(context,tcx,signature),
                                    "extra_argument_types":extra.iter().map(|ty|type_json(context,tcx,ty)).collect::<Vec<_>>(),
                                    "fn_abi":fn_abi_json(context,tcx,abi)})
                                }
                                Err(error) => {
                                    json!({"status":"unsupported","kind":"indirect_function_pointer_abi_error","error_debug":format!("{error:?}")})
                                }
                            }
                        }
                        None => unavailable_compiler_fact(
                            "indirect call has fewer arguments than its normalized signature",
                        ),
                    }
                }
                Err(error) => {
                    json!({"status":"unsupported","kind":"indirect_signature_normalization_error","error_debug":format!("{error:?}")})
                }
            }
        }
        _ => {
            json!({"status":"unknown","kind":"indirect_or_non_fn_def","function_type":type_json(context, tcx,func_ty)})
        }
    }
}

fn fn_abi_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    abi: &rustc_target::callconv::FnAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
) -> Value {
    json!({"calling_convention":canon_abi_json(abi.conv),"c_variadic":abi.c_variadic,"fixed_count":abi.fixed_count,"can_unwind":abi.can_unwind,"return":arg_abi_json(context, tcx,&abi.ret),"arguments":abi.args.iter().map(|arg|arg_abi_json(context, tcx,arg)).collect::<Vec<_>>()})
}

fn arg_attributes_json(attrs: rustc_target::callconv::ArgAttributes) -> Value {
    use rustc_target::callconv::ArgAttribute as A;
    let captures = if attrs.regular.contains(A::CapturesNone) {
        json!({"kind":"none"})
    } else if attrs.regular.contains(A::CapturesAddress) {
        json!({"kind":"address"})
    } else if attrs.regular.contains(A::CapturesReadOnly) {
        json!({"kind":"read_only"})
    } else {
        json!({"kind":"unrestricted"})
    };
    json!({
        "status":"supported",
        "regular_bits":attrs.regular.bits(),
        "captures":captures,
        "no_alias":attrs.regular.contains(A::NoAlias),
        "non_null":attrs.regular.contains(A::NonNull),
        "read_only":attrs.regular.contains(A::ReadOnly),
        "in_register":attrs.regular.contains(A::InReg),
        "no_undef":attrs.regular.contains(A::NoUndef),
        "writable":attrs.regular.contains(A::Writable),
        "no_free":attrs.regular.contains(A::NoFree),
        "arg_extension":arg_extension_json(attrs.arg_ext),
        "pointee_size_bytes":attrs.pointee_size.bytes(),
        "pointee_align_bytes":attrs.pointee_align.map(|align|align.bytes())
    })
}

fn reg_json(reg: rustc_abi::Reg) -> Value {
    use rustc_abi::RegKind;
    let kind = match reg.kind {
        RegKind::Integer => json!({"kind":"integer"}),
        RegKind::Float => json!({"kind":"float"}),
        RegKind::PpcF128 => json!({"kind":"ppc_f128"}),
        RegKind::Vector { hint_vector_elem } => {
            json!({"kind":"vector","hint_element":primitive_json_untyped(hint_vector_elem)})
        }
    };
    json!({"kind":kind,"size_bits":reg.size.bits()})
}

fn primitive_json_untyped(primitive: rustc_abi::Primitive) -> Value {
    use rustc_abi::Primitive;
    match primitive {
        Primitive::Int(integer, signed) => {
            json!({"kind":"integer","integer_kind":integer.int_ty_str(),"signed":signed,"size_bytes":integer.size().bytes()})
        }
        Primitive::Float(float) => {
            json!({"kind":"float","float_kind":float.ty_str(),"size_bytes":float.size().bytes()})
        }
        Primitive::Pointer(address_space) => {
            json!({"kind":"pointer","address_space":address_space.0})
        }
    }
}

fn cast_target_json(cast: &rustc_target::callconv::CastTarget) -> Value {
    json!({
        "prefix_registers":cast.prefix.iter().copied().map(reg_json).collect::<Vec<_>>(),
        "rest_offset_bytes":cast.rest_offset.map(|offset|offset.bytes()),
        "rest_register":reg_json(cast.rest.unit),
        "rest_total_bytes":cast.rest.total.bytes(),
        "rest_is_consecutive":cast.rest.is_consecutive,
        "attributes":arg_attributes_json(cast.attrs)
    })
}

fn arg_abi_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    arg: &rustc_target::callconv::ArgAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
) -> Value {
    use rustc_target::callconv::PassMode as P;
    let mode = match &arg.mode {
        P::Ignore => json!({"kind":"Ignore"}),
        P::Direct(attrs) => json!({"kind":"Direct","attributes":arg_attributes_json(*attrs)}),
        P::Pair(a, b) => {
            json!({"kind":"Pair","first":arg_attributes_json(*a),"second":arg_attributes_json(*b)})
        }
        P::Cast {
            pad_i32_count,
            cast,
        } => json!({"kind":"Cast","pad_i32_count":pad_i32_count,"target":cast_target_json(cast)}),
        P::Indirect {
            attrs,
            address_space,
            mode,
        } => {
            json!({"kind":"Indirect","attributes":arg_attributes_json(*attrs),"address_space":address_space.map(|space|space.0),"mode":indirect_mode_json(*mode)})
        }
        P::IndirectUnsized { attrs, meta_attrs } => {
            json!({"kind":"IndirectUnsized","attributes":arg_attributes_json(*attrs),"metadata_attributes":arg_attributes_json(*meta_attrs)})
        }
    };
    json!({
        "type":type_json(context, tcx,arg.layout.ty),
        "layout":layout_value_json(tcx, arg.layout),
        "mode":mode
    })
}

fn const_operand_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &rustc_middle::mir::ConstOperand<'tcx>,
) -> Value {
    use rustc_middle::mir::Const;
    let ty = operand.const_.ty();
    let source = match operand.const_ {
        Const::Ty(ty, value) => json!({
            "kind":"type_system_const",
            "type":type_json(context, tcx,ty),
            "const":const_type_json(context,tcx,value),
        }),
        Const::Unevaluated(value, ty) => json!({
            "kind":"unevaluated",
            "def_id":def_json(value.def), "def_path":tcx.def_path_str(value.def),
            "generic_args":generic_args_json(context, tcx,value.args),
            "promoted":value.promoted.map(|id|id.as_u32()), "type":type_json(context, tcx,ty)
        }),
        Const::Val(_, _) => json!({"kind":"already_evaluated"}),
    };
    let evaluated = operand.const_.eval(tcx, body.typing_env(tcx), operand.span);
    let value = match evaluated {
        Ok(value) => const_value_json(context, tcx, ty, value),
        Err(error) => json!({
            "status":"unsupported",
            "kind":"const_evaluation_error",
            "type":type_json(context,tcx,ty),
            "error_debug":format!("{error:?}"),
        }),
    };
    let status = value
        .get("status")
        .and_then(Value::as_str)
        .unwrap_or("unsupported");
    let constant = json!({"status":status,"kind":"evaluated_const","source":source,"value":value});
    json!({
        "status": status,
        "type": type_json(context, tcx, ty),
        "user_type_annotation": operand.user_ty.map(|value| json!({"status":"supported","kind":"annotation_ref","index":value.as_u32()})),
        "constant": constant,
        "span": span_json(tcx, operand.span),
    })
}

fn const_value_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    value: rustc_middle::mir::ConstValue,
) -> Value {
    use rustc_middle::mir::ConstValue;
    match value {
        ConstValue::ZeroSized => json!({
            "status":"supported",
            "kind":"zero_sized",
            "type":type_json(context,tcx,ty),
        }),
        ConstValue::Scalar(scalar) => {
            // `Scalar` is an integer-or-pointer value independently of the
            // enclosing MIR type. In particular, ADTs with pointer niches can
            // carry `Scalar::Ptr` (for example `io::Error` constants). Miri's
            // const_val_to_op preserves that variant and only adjusts pointer
            // roots; converting it to bits here would both lose provenance
            // and fail with ReadPointerAsInt. CtfeProvenance has
            // OFFSET_IS_ADDR=false, so try_to_scalar_int distinguishes those
            // pointer scalars without permitting a ptr-to-int conversion.
            let scalar_has_provenance = scalar.try_to_scalar_int().is_err();
            if matches!(*ty.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::FnPtr(..))
                || scalar_has_provenance
            {
                scalar_pointer_json(context, tcx, ty, scalar)
            } else {
                let size = tcx
                    .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
                    .ok()
                    .map(|layout| layout.size);
                let conversion = size.map(|size| scalar.to_bits(size).report_err());
                match conversion {
                    Some(Ok(bits)) => json!({
                        "status":"supported",
                        "kind":"scalar",
                        "type":type_json(context,tcx,ty),
                        "bits_unsigned":bits.to_string(),
                    }),
                    Some(Err(error)) => json!({
                        "status":"unsupported",
                        "kind":"scalar_with_provenance_or_invalid_bits",
                        "type":type_json(context,tcx,ty),
                        "conversion_error":format!("{error:?}"),
                    }),
                    None => json!({
                        "status":"unsupported",
                        "kind":"scalar_layout_unavailable",
                        "type":type_json(context,tcx,ty),
                    }),
                }
            }
        }
        ConstValue::Slice { alloc_id, meta } => {
            let allocation = allocation_ref(context, tcx, alloc_id);
            json!({
                "status":allocation_status(context, &allocation),
                "kind":"slice_allocation",
                "type":type_json(context,tcx,ty),
                "allocation":allocation,
                "metadata_length":meta,
            })
        }
        ConstValue::Indirect { alloc_id, offset } => {
            let allocation = allocation_ref(context, tcx, alloc_id);
            json!({
                "status":allocation_status(context, &allocation),
                "kind":"indirect_allocation",
                "type":type_json(context,tcx,ty),
                "allocation":allocation,
                "offset_bytes":offset.bytes(),
            })
        }
    }
}

// These are source compiler queries, not conclusions inferred from an
// initializer image, a Rust type spelling or the target triple.
fn static_global_info_json(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> Value {
    let nested = match tcx.def_kind(def) {
        rustc_hir::def::DefKind::Static { nested, .. } => nested,
        _ => unreachable!("static global metadata requires a static definition"),
    };
    let global = GlobalAlloc::Static(def);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let (size, align) = global.size_and_align(tcx, typing_env);
    let mutable = global.mutability(tcx, typing_env);
    json!({"status":"supported","size_bytes":size.bytes(),"align_bytes":align.bytes(),
        "mutability":match mutable { rustc_ast::Mutability::Mut => "mutable", rustc_ast::Mutability::Not => "immutable" },
        "is_static":tcx.is_static(def),"is_foreign_item":tcx.is_foreign_item(def),"nested":nested,
        "thread_local":tcx.is_thread_local_static(def)})
}

fn scalar_pointer_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    scalar: rustc_middle::mir::interpret::Scalar,
) -> Value {
    let pointer = scalar.to_pointer(&tcx.data_layout);
    let (provenance, offset) = pointer.into_raw_parts();
    match provenance {
        Some(provenance) => {
            let (alloc_id, immutable, shared_ref) = provenance.into_parts();
            let allocation = allocation_ref(context, tcx, alloc_id);
            json!({
                "status":allocation_status(context, &allocation),
                "kind":"pointer_scalar",
                "type":type_json(context,tcx,ty),
                "allocation":allocation,
                "offset_bytes":offset.bytes(),
                "immutable":immutable,
                "shared_ref":shared_ref,
            })
        }
        None => json!({
            "status":"supported",
            "kind":"pointer_scalar_without_provenance",
            "type":type_json(context,tcx,ty),
            "address":offset.bytes().to_string(),
            "address_width_bytes":tcx.data_layout.pointer_size().bytes(),
        }),
    }
}

fn allocation_status(context: &ExportContext<'_>, allocation_ref: &Value) -> &'static str {
    let Some(id) = allocation_ref.get("allocation_id").and_then(Value::as_u64) else {
        return "unsupported";
    };
    match context
        .allocation_nodes
        .get(&id)
        .and_then(|node| node.get("status"))
        .and_then(Value::as_str)
    {
        Some("supported") => "supported",
        _ => "unsupported",
    }
}

fn allocation_ref<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    alloc_id: AllocId,
) -> Value {
    let id = context.allocation_id(alloc_id);
    if context.allocation_nodes.contains_key(&id)
        || context.allocations_in_progress.contains(&alloc_id)
    {
        return json!({"allocation_id":id});
    }
    context.allocations_in_progress.insert(alloc_id);
    let mut node = match tcx.try_get_global_alloc(alloc_id) {
        None => {
            json!({"allocation_id":id,"status":"unsupported","kind":"missing_global_allocation"})
        }
        Some(GlobalAlloc::Memory(memory)) => {
            let mut node = allocation_memory_payload(context, tcx, memory.inner());
            let object = node.as_object_mut().expect("memory payload is an object");
            object.insert("allocation_id".into(), json!(id));
            object.insert("status".into(), json!("supported"));
            object.insert("kind".into(), json!("memory"));
            node
        }
        Some(GlobalAlloc::Function { instance }) => {
            let instance_id = context.register_instance(instance);
            json!({
                "allocation_id":id,
                "status":"supported",
                "kind":"function",
                "instance_id":instance_id,
                "instance_def_id":def_json(instance.def.def_id()),
                "instance_def_path":tcx.def_path_str(instance.def.def_id()),
                "generic_args":generic_args_json(context,tcx,instance.args),
            })
        }
        Some(GlobalAlloc::Static(def)) => {
            let global_info = static_global_info_json(tcx, def);
            if tcx.is_foreign_item(def) {
                // rustc has no initializer for an extern static. Preserve its
                // compiler allocation identity and declaration metadata so
                // Miri's extern_static_pointer resolver can produce the
                // runtime pointer. Never ask eval_static_initializer here:
                // that query ICEs for foreign DefIds on the pinned compiler.
                json!({
                    "allocation_id":id,
                    "status":"supported",
                    "kind":"static",
                    "def_id":def_json(def),
                    "def_path":tcx.def_path_str(def),
                    "thread_local":tcx.is_thread_local_static(def),
                    "global_info":global_info,
                })
            } else {
                match tcx.eval_static_initializer(def) {
                    Ok(initializer) => json!({
                        "allocation_id":id,
                        "status":"supported",
                        "kind":"static",
                        "def_id":def_json(def),
                        "def_path":tcx.def_path_str(def),
                        "thread_local":tcx.is_thread_local_static(def),
                        "global_info":global_info,
                        "initializer":allocation_memory_payload(context,tcx,initializer.inner()),
                    }),
                    Err(error) => json!({
                        "allocation_id":id,
                        "status":"unsupported",
                        "kind":"static_initializer_error",
                        "def_id":def_json(def),
                        "def_path":tcx.def_path_str(def),
                        "thread_local":tcx.is_thread_local_static(def),
                        "global_info":global_info,
                        "error_debug":format!("{error:?}"),
                    }),
                }
            }
        }
        Some(GlobalAlloc::VTable(ty, predicates)) => {
            let predicate_json = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Vec<_>>();
            let principal = predicates
                .principal()
                .map(|principal| tcx.instantiate_bound_regions_with_erased(principal));
            let entries = if let Some(principal) = principal {
                tcx.vtable_entries(principal.with_self_ty(tcx, ty))
            } else {
                TyCtxt::COMMON_VTABLE_ENTRIES
            };
            let entry_json = entries
                .iter()
                .map(|entry| match *entry {
                    ty::VtblEntry::MetadataDropInPlace => {
                        if ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
                            let instance = ty::Instance::resolve_drop_glue(tcx, ty);
                            let instance_id = context.register_instance(instance);
                            json!({"status":"supported","kind":"drop_in_place","instance_id":instance_id})
                        } else {
                            json!({"status":"supported","kind":"drop_in_place_null"})
                        }
                    }
                    ty::VtblEntry::MetadataSize => {
                        json!({"status":"supported","kind":"size_bytes"})
                    }
                    ty::VtblEntry::MetadataAlign => {
                        json!({"status":"supported","kind":"align_bytes"})
                    }
                    ty::VtblEntry::Vacant => json!({"status":"supported","kind":"vacant"}),
                    ty::VtblEntry::Method(instance) => {
                        let instance_id = context.register_instance(instance);
                        json!({
                            "status":"supported",
                            "kind":"method",
                            "instance_id":instance_id,
                            "def_id":def_json(instance.def.def_id()),
                            "def_path":tcx.def_path_str(instance.def.def_id()),
                            "generic_args":generic_args_json(context,tcx,instance.args),
                        })
                    }
                    ty::VtblEntry::TraitVPtr(trait_ref) => {
                        let existential = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);
                        let vtable_alloc = tcx.vtable_allocation((ty, Some(existential)));
                        json!({
                            "status":"supported",
                            "kind":"supertrait_vtable_pointer",
                            "trait_def_id":def_json(trait_ref.def_id),
                            "trait_def_path":tcx.def_path_str(trait_ref.def_id),
                            "generic_args":generic_args_json(context,tcx,trait_ref.args),
                            "allocation":allocation_ref(context,tcx,vtable_alloc),
                        })
                    }
                })
                .collect::<Vec<_>>();
            let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty));
            let (size_bytes, align_bytes, layout_status) = match layout {
                Ok(layout) => (
                    Some(layout.size.bytes()),
                    Some(layout.align.abi.bytes()),
                    "supported",
                ),
                Err(_) => (None, None, "unsupported"),
            };
            let children_supported = predicate_json
                .iter()
                .chain(entry_json.iter())
                .all(|node| node.get("status").and_then(Value::as_str) == Some("supported"));
            let status = if children_supported && layout_status == "supported" {
                "supported"
            } else {
                "unsupported"
            };
            json!({
                "allocation_id":id,
                "status":status,
                "kind":"vtable",
                "type":type_json(context,tcx,ty),
                "size_bytes":size_bytes,
                "align_bytes":align_bytes,
                "layout_status":layout_status,
                "predicates":predicate_json,
                "principal_predicate":predicates.principal().map(|p|existential_predicate_json(context,tcx,p.map_bound(ty::ExistentialPredicate::Trait))),
                "entries":entry_json,
            })
        }
        Some(GlobalAlloc::TypeId { ty }) => json!({
            "allocation_id":id,
            "status":"supported",
            "kind":"type_id",
            "type":type_json(context,tcx,ty),
        }),
    };
    // Preserve rustc's actual `AllocId.0.get()` independently of the
    // compilation-local graph ID. Consumers may use this only as source
    // identity evidence; it is not stable across compilations and must never
    // be reconstructed from `id`.
    if let Some(object) = node.as_object_mut() {
        object.insert("source_alloc_id".into(), json!(alloc_id.0.get()));
    }
    context.allocations_in_progress.remove(&alloc_id);
    context.allocation_nodes.insert(id, node);
    json!({"allocation_id":id})
}

fn bound_variable_json(tcx: TyCtxt<'_>, kind: ty::BoundVariableKind<'_>) -> Value {
    match kind {
        ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon) => {
            json!({"kind":"type","type_kind":{"kind":"anonymous"}})
        }
        ty::BoundVariableKind::Ty(ty::BoundTyKind::Param(def)) => {
            json!({"kind":"type","type_kind":{"kind":"parameter","def_id":def_json(def)}})
        }
        ty::BoundVariableKind::Region(region) => {
            json!({"kind":"region","region_kind":bound_region_kind_json(tcx,region)})
        }
        ty::BoundVariableKind::Const => json!({"kind":"const"}),
    }
}

fn existential_predicate_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    predicate: ty::PolyExistentialPredicate<'tcx>,
) -> Value {
    let id = context.predicate_id(predicate);
    let mut payload = existential_predicate_payload_json(context, tcx, predicate);
    let obj = payload
        .as_object_mut()
        .expect("predicate payload is object");
    obj.insert("predicate_id".into(), json!(id));
    obj.insert(
        "bound_variables".into(),
        json!(
            predicate
                .bound_vars()
                .iter()
                .map(|bound| bound_variable_json(tcx, bound))
                .collect::<Vec<_>>()
        ),
    );
    payload
}

// Source interpret/traits.rs::check_vtable_for_type sorts skip_binder values,
// dedups full binders, then normalizes after late-bound-region erasure.
fn compiler_predicate_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut records = Vec::new();
    let mut cursor = 0;
    while cursor < context.pending_predicates.len() {
        let predicate = context.pending_predicates[cursor];
        let original = existential_predicate_json(context, tcx, predicate);
        let erased = tcx.instantiate_bound_regions_with_erased(predicate);
        let normalization = if erased.has_non_region_param()
            || erased.has_escaping_bound_vars()
            || erased.has_infer()
            || erased.has_placeholders()
            || erased.references_error()
        {
            unavailable_compiler_fact(
                "predicate requires complete caller instantiation environment",
            )
        } else {
            match tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(erased)) {
                Ok(value) => compiler_fact(json!(context.predicate_id(ty::Binder::dummy(value)))),
                Err(error) => {
                    json!({"status":"unsupported","value":null,"reason":"predicate normalization failed","error_debug":format!("{error:?}")})
                }
            }
        };
        records.push(
            json!({"predicate_id":cursor,"typing_env":"fully_monomorphized",
            "auto_trait":matches!(predicate.skip_binder(),ty::ExistentialPredicate::AutoTrait(_)),
            "original":original,"normalization":normalization}),
        );
        cursor += 1;
    }
    let mut ordered = context.pending_predicates.clone();
    ordered.sort_by(|a, b| a.skip_binder().stable_cmp(tcx, &b.skip_binder()));
    let mut rank = 0u64;
    let mut previous = None;
    for predicate in ordered {
        if let Some(previous) = previous {
            if predicate.skip_binder().stable_cmp(tcx, &previous) != std::cmp::Ordering::Equal {
                rank += 1;
            }
        }
        let id = context.predicate_ids[&predicate] as usize;
        records[id]["stable_key"] = json!(rank);
        previous = Some(predicate.skip_binder());
    }
    json!(records)
}

fn existential_predicate_payload_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    predicate: ty::PolyExistentialPredicate<'tcx>,
) -> Value {
    match predicate.skip_binder() {
        ty::ExistentialPredicate::Trait(trait_ref) => json!({
            "status":"supported",
            "kind":"trait",
            "def_id":def_json(trait_ref.def_id),
            "def_path":tcx.def_path_str(trait_ref.def_id),
            "generic_args":generic_args_json(context,tcx,trait_ref.args),
        }),
        ty::ExistentialPredicate::AutoTrait(def) => json!({
            "status":"supported",
            "kind":"auto_trait",
            "def_id":def_json(def),
            "def_path":tcx.def_path_str(def),
        }),
        ty::ExistentialPredicate::Projection(projection) => {
            let term = match projection.term.kind() {
                ty::TermKind::Ty(value) => json!({
                    "status":"supported",
                    "kind":"type",
                    "value":type_json(context,tcx,value),
                }),
                ty::TermKind::Const(value) => json!({
                    "status":"unsupported",
                    "kind":"const",
                    "value":const_type_json(context,tcx,value),
                }),
            };
            let status = term
                .get("status")
                .and_then(Value::as_str)
                .unwrap_or("unsupported");
            json!({
                "status":status,
                "kind":"projection",
                "def_id":def_json(projection.def_id),
                "def_path":tcx.def_path_str(projection.def_id),
                "generic_args":generic_args_json(context,tcx,projection.args),
                "term":term,
            })
        }
    }
}

fn allocation_memory_payload<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    allocation: &rustc_middle::mir::interpret::Allocation,
) -> Value {
    let bytes = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
    let initialized_ranges = allocation
        .init_mask()
        .range_as_init_chunks(rustc_middle::mir::interpret::AllocRange::from(
            rustc_abi::Size::ZERO..allocation.size(),
        ))
        .map(|chunk| {
            let range = chunk.range();
            json!({
                "state": if chunk.is_init() { "initialized" } else { "uninitialized" },
                "start_bytes": range.start.bytes(),
                "end_bytes_exclusive": range.end.bytes(),
            })
        })
        .collect::<Vec<_>>();
    let pointer_size = tcx.data_layout.pointer_size().bytes_usize();
    let relocations = allocation
        .provenance()
        .ptrs()
        .iter()
        .map(|(offset, provenance)| {
            let start = offset.bytes_usize();
            let end = start + pointer_size;
            let (target_alloc, immutable, shared_ref) = provenance.into_parts();
            let target = allocation_ref(context, tcx, target_alloc);
            json!({
                "storage_offset_bytes": offset.bytes(),
                "target": target,
                "target_offset_encoded_bytes": bytes_hex(&bytes[start..end]),
                "immutable": immutable,
                "shared_ref": shared_ref,
            })
        })
        .collect::<Vec<_>>();
    let mutability = match allocation.mutability {
        rustc_ast::Mutability::Mut => "mutable",
        rustc_ast::Mutability::Not => "immutable",
    };
    json!({
        "size_bytes":allocation.size().bytes(),
        "align_bytes":allocation.align.bytes(),
        "mutability":mutability,
        "bytes_hex":bytes_hex(bytes),
        "initialization_ranges":initialized_ranges,
        "relocations":relocations,
    })
}

fn bytes_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(output, "{byte:02x}").expect("writing into a String cannot fail");
    }
    output
}

// Exact interpret/call.rs type constructors and resolve_drop_glue. Query only
// type nodes demanded by serialized source MIR/signatures/metadata. Pointer and
// reference constructor results are output nodes, not fresh source demands.
// Newly reached drop-glue MIR can add more demands for a later finite wave.
fn compiler_runtime_type_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    processed: &mut HashSet<ty::Ty<'tcx>>,
) -> Value {
    let mut types = context
        .runtime_type_query_demands
        .iter()
        .filter(|ty| !processed.contains(ty))
        .filter_map(|ty| context.type_ids.get(ty).map(|id| (*id, *ty)))
        .collect::<Vec<_>>();
    types.sort_by_key(|(id, _)| *id);
    let records=types.into_iter().map(|(id,input)| {
        processed.insert(input);
        let closed=!input.has_non_region_param() && !input.has_escaping_bound_vars()
            && !input.has_infer() && !input.has_placeholders() && !input.references_error();
        let normalized=if closed {tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(),ty::Unnormalized::new_wip(input)).ok()} else {None};
        let drop=match normalized {
            Some(ty) if tcx.lang_items().get(rustc_attr_ir::LangItem::DropGlue).is_some()=> {
                let instance=ty::Instance::resolve_drop_glue(tcx,ty);
                // rustc represents an empty drop operation as DropGlue(None).
                // It is a source no-op and has no MIR to traverse; identity
                // registration avoids inventing MIR type demands from it.
                let instance_id=if matches!(instance.def,
                    ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, None))) {
                    let already_reached = context.pending_instances.contains(&instance)
                        || context.emitted_instances.contains(&instance);
                    let id = context.register_instance_identity(instance);
                    if !already_reached {
                        context.runtime_query_only_empty_drops.insert(instance);
                    }
                    id
                } else {
                    context.register_instance(instance)
                };
                compiler_fact(json!({"instance_id":instance_id,
                    "instance_kind":instance_kind_json(context,tcx,instance.def),
                    "generic_args":generic_args_json(context,tcx,instance.args)}))
            }
            _=>unavailable_compiler_fact("drop glue requires normalized monomorphic type and drop_in_place lang item"),
        };
        json!({"input_type_id":id,"typing_env":"fully_monomorphized",
            "mut_pointer_type":compiler_fact(query_generated_type_json(context,tcx,ty::Ty::new_mut_ptr(tcx,input))),
            "mut_reference_type":compiler_fact(query_generated_type_json(context,tcx,ty::Ty::new_mut_ref(tcx,tcx.lifetimes.re_erased,input))),
            "drop_glue":drop})
    }).collect::<Vec<_>>();
    Value::Array(records)
}

fn compiler_runtime_virtual_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    // call.rs::assert_virtual_instance_matches_concrete: preserve original
    // complete virtual args and use rustc from_assoc/erase_self_ty/rebase_onto.
    let mut virtuals = context
        .instance_ids
        .iter()
        .filter_map(|(instance, id)| match instance.def {
            ty::InstanceKind::Virtual(def, _) => Some((*id, *instance, def)),
            _ => None,
        })
        .collect::<Vec<_>>();
    virtuals.sort_by_key(|(id, _, _)| *id);
    let mut concrete_pairs = context.vtable_query_requests.clone();
    for alloc in context.allocation_ids.keys() {
        if let Some(GlobalAlloc::VTable(ty, predicates)) = tcx.try_get_global_alloc(*alloc) {
            concrete_pairs.insert((ty, predicates));
        }
    }
    let mut concrete = concrete_pairs.into_iter().collect::<Vec<_>>();
    concrete.sort_by_key(|(ty, predicates)| format!("{ty:?}|{predicates:?}"));
    for (ty, predicates) in concrete.iter().copied() {
        context.type_id(ty);
        for predicate in predicates.iter() {
            context.predicate_id(predicate);
        }
    }
    concrete.sort_by_key(|(ty, predicates)| {
        (
            context.type_id(*ty),
            predicates
                .iter()
                .map(|p| context.predicate_id(p))
                .collect::<Vec<_>>(),
        )
    });
    let mut virtual_queries = Vec::new();
    for (original_instance_id, original, def) in virtuals {
        for (concrete, predicates) in concrete.iter().copied() {
            let parent = tcx.parent(def);
            let trait_ref = ty::TraitRef::from_assoc(tcx, parent, original.args);
            let existential = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);
            let rebound = original.args.rebase_onto(
                tcx,
                parent,
                existential.with_self_ty(tcx, concrete).args,
            );
            let input_type = type_json(context, tcx, concrete);
            let input_type_id = context.type_id(concrete);
            let input_predicates = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Vec<_>>();
            let input_predicate_ids = predicates
                .iter()
                .map(|predicate| context.predicate_id(predicate))
                .collect::<Vec<_>>();
            let closed = !rebound.has_non_region_param()
                && !rebound.has_escaping_bound_vars()
                && !rebound.has_infer()
                && !rebound.has_placeholders()
                && !rebound.references_error();
            let signature = tcx.fn_sig(def).instantiate_identity().skip_norm_wip();
            let vtable_shim = !signature.inputs().skip_binder().is_empty()
                && signature.input(0).skip_binder().is_param(0)
                && tcx.generics_of(def).has_self;
            let resolved = if closed {
                let probe = if vtable_shim {
                    Ok(Some(ty::Instance {
                        def: ty::InstanceKind::Shim(ty::ShimKind::VTable(def)),
                        args: rebound,
                    }))
                } else {
                    ty::Instance::try_resolve(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        def,
                        rebound,
                    )
                };
                match probe {
                    Ok(Some(_)) => {
                        let instance = ty::Instance::expect_resolve_for_vtable(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            def,
                            rebound,
                            rustc_span::DUMMY_SP,
                        );
                        let id = context.register_instance(instance);
                        compiler_fact(
                            json!({"instance_id":id,"instance_kind":instance_kind_json(context,tcx,instance.def),"generic_args":generic_args_json(context,tcx,instance.args)}),
                        )
                    }
                    Ok(None) => unavailable_compiler_fact(
                        "rustc virtual target resolution returned no instance",
                    ),
                    Err(error) => {
                        json!({"status":"unsupported","reason":"rustc virtual target resolution failed","error_debug":format!("{error:?}")})
                    }
                }
            } else {
                unavailable_compiler_fact(
                    "virtual target query requires complete monomorphic arguments",
                )
            };
            virtual_queries.push(json!({"typing_env":"fully_monomorphized",
                "original_instance_id":original_instance_id,
                "original":{"instance_kind":instance_kind_json(context,tcx,original.def),"generic_args":generic_args_json(context,tcx,original.args)},
                "method_definition":def_json(def),"parent_trait":def_json(parent),
                "concrete_type":input_type,
                "rebased_args":generic_args_json(context,tcx,rebound),"resolved":resolved,
                "vtable_query":{"status":"supported","input_type":type_json(context,tcx,concrete),
                    "input_predicates":input_predicates,
                    "_query_key":{"input_type_id":input_type_id,"input_predicate_ids":input_predicate_ids}}}));
        }
    }
    Value::Array(virtual_queries)
}

fn compiler_caller_location_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let mut instances = context
        .instance_ids
        .iter()
        .filter(|(instance, _)| !context.symbol_only_instances.contains(instance))
        .map(|(instance, id)| (*id, *instance))
        .collect::<Vec<_>>();
    instances.sort_by_key(|(id, _)| *id);
    Value::Array(instances.into_iter().map(|(id,instance)|json!({
        "instance_id":id,"instance_kind":instance_kind_json(context,tcx,instance.def),
        "generic_args":generic_args_json(context,tcx,instance.args),
        "requires_caller_location":instance.def.requires_caller_location(tcx),
        "display":instance.to_string(),
        "inline_never":matches!(tcx.codegen_instance_attrs(instance.def).inline,rustc_attr_ir::InlineAttr::Never),
        "target_features":tcx.codegen_instance_attrs(instance.def).target_features.iter().map(|feature|json!({
            "name":feature.name.as_str(),"kind":match feature.kind {
                rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Implied=>"implied",
                rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Enabled=>"enabled",
                rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Forced=>"forced",
            }})).collect::<Vec<_>>(),
        "item_name":match tcx.opt_item_name(instance.def_id()) {
            Some(name)=>compiler_fact(json!(name.as_str())),
            None=>unavailable_compiler_fact("compiler definition has no item name"),
        },
        "intrinsic_metadata":intrinsic_metadata_json(tcx,instance.def_id()),
        "is_foreign_item":tcx.is_foreign_item(instance.def_id()),
        "is_closure_like":tcx.is_closure_like(instance.def_id()),
        "codegen_symbol_name":if tcx.def_kind(instance.def_id()).has_codegen_attrs(){
            compiler_fact(json!(tcx.codegen_fn_attrs(instance.def_id()).symbol_name.map(|symbol|symbol.as_str().to_owned())))
        }else{unavailable_compiler_fact("definition does not support codegen attributes")},
        "symbol_name":if instance.args.has_non_region_param() || instance.args.has_escaping_bound_vars()
            || instance.args.has_infer() || instance.args.has_placeholders() || matches!(instance.def,ty::InstanceKind::Virtual(..))
            || !matches!(tcx.def_kind(instance.def_id()),rustc_hir::def::DefKind::Fn|rustc_hir::def::DefKind::AssocFn|rustc_hir::def::DefKind::Closure|rustc_hir::def::DefKind::SyntheticCoroutineBody) {
            unavailable_compiler_fact("symbol name requires a complete concrete callable instance")
        }else{compiler_fact(json!(tcx.symbol_name(instance).name))}
    })).collect::<Vec<_>>())
}

fn compiler_frame_metadata_json(tcx: TyCtxt<'_>) -> Value {
    let local = rustc_hir::def_id::LOCAL_CRATE;
    let mut crates = tcx.crates(()).iter().copied().collect::<Vec<_>>();
    crates.push(local);
    crates.sort_by_key(|krate| krate.as_u32());
    crates.dedup();
    json!({"local_crate":local.as_u32(),"crates":crates.into_iter().map(|krate|
        json!({"crate":krate.as_u32(),"name":tcx.crate_name(krate).as_str()})).collect::<Vec<_>>()})
}

// FnAbiOf::fn_abi_of_instance. Complete instance+extra-argument vector+env is
// the query key; empty arguments are also recorded for runtime drop/vtable calls.
fn compiler_instance_abis_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let mut requests = context.instance_abi_requests.clone();
    for instance in context.instance_ids.keys() {
        if context.runtime_query_only_empty_drops.contains(instance) {
            continue;
        }
        requests.insert((*instance, ty::List::empty()));
        // call.rs deliberately queries Item ABI for Rust intrinsics which fall
        // back to a body; the Intrinsic kind's ABI is not interchangeable.
        if let ty::InstanceKind::Intrinsic(def) = instance.def {
            requests.insert((
                ty::Instance {
                    def: ty::InstanceKind::Item(def),
                    args: instance.args,
                },
                ty::List::empty(),
            ));
        }
    }
    requests.retain(|(instance, _)| !context.runtime_query_only_empty_drops.contains(instance));
    let mut requests = requests.into_iter().collect::<Vec<_>>();
    requests.sort_by_key(|(instance, extra)| {
        (
            context.instance_ids.get(instance).copied(),
            tcx.def_path_str(instance.def_id()),
            extra
                .iter()
                .map(|ty| context.type_id(ty))
                .collect::<Vec<_>>(),
        )
    });
    let records=requests.into_iter().map(|(instance,extra)|{
        let closed=!instance.args.has_non_region_param() && !instance.args.has_escaping_bound_vars()
            && !instance.args.has_infer() && !instance.args.has_placeholders()
            && !extra.has_non_region_param() && !extra.has_escaping_bound_vars()
            && !extra.has_infer() && !extra.has_placeholders();
        let function=matches!(tcx.def_kind(instance.def_id()),rustc_hir::def::DefKind::Fn|rustc_hir::def::DefKind::AssocFn|rustc_hir::def::DefKind::Closure|rustc_hir::def::DefKind::SyntheticCoroutineBody);
        let abi=if matches!(instance.def,ty::InstanceKind::LlvmIntrinsic(_)){
            unavailable_compiler_fact("source FnAbi query is not defined for LLVM intrinsic instances")
        }else if !closed || !function {
            unavailable_compiler_fact("FnAbi instance query requires a complete monomorphic function instance and extra argument vector")
        }else{match tcx.fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((instance,extra))){
                Ok(abi)=>compiler_fact(fn_abi_json(context,tcx,abi)),
            Err(error)=>json!({"status":"unsupported","reason":"rustc fn_abi_of_instance failed","error_debug":format!("{error:?}")}),
        }};
        let mut record=json!({"typing_env":"fully_monomorphized",
            "instance_kind":instance_kind_json(context,tcx,instance.def),
            "generic_args":generic_args_json(context,tcx,instance.args),
            "extra_argument_types":extra.iter().map(|ty|type_json(context,tcx,ty)).collect::<Vec<_>>(),
            "abi_query":abi});
        // Intrinsic fallback Item ABI keys need not have a separately emitted
        // instance-MIR graph node. Omit that optional graph reference, retaining
        // the complete actual instance key; null is not a valid instance ID.
        if let Some(id)=context.instance_ids.get(&instance){record["instance_id"]=json!(id);}
        record
    }).collect::<Vec<_>>();
    Value::Array(records)
}

// backtrace.rs::handle_miri_get_backtrace and resolve_frame_pointer. The table
// covers compiler-produced frame positions only. Forged/unseen byte positions
// require additional source-map evidence; consumers must never guess a line.
fn backtrace_spans_json(tcx: TyCtxt<'_>, body: &rustc_middle::mir::Body<'_>) -> Value {
    let mut spans = vec![body.span, tcx.def_span(body.source.def_id())];
    for local in body.local_decls.iter() {
        spans.push(local.source_info.span);
    }
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            spans.push(statement.source_info.span);
        }
        if let Some(terminator) = &block.terminator {
            spans.push(terminator.source_info.span);
        }
    }
    let mut seen = HashSet::new();
    let records = spans
        .into_iter()
        .filter(|span| seen.insert(*span))
        .map(|span| {
            let collapsed = rustc_span::hygiene::walk_chain_collapsed(span, body.span);
            let position = tcx.sess.source_map().lookup_char_pos(collapsed.lo());
            json!({"span":span_json(tcx,span),"collapsed_lo":collapsed.lo().0,
            "source_position":{"byte_position":collapsed.lo().0,"line":position.line,
                "zero_based_char_column":position.col.0,
                "filename":position.file.name.prefer_remapped_unconditionally().to_string()}})
        })
        .collect::<Vec<_>>();
    Value::Array(records)
}

// stack.rs::push_stack_frame post-monomorphization required constant checks.
// Retain exact source order, normalized constants and eval query results.
fn required_constant_checks_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    instance: ty::Instance<'tcx>,
    already_instantiated: bool,
    context: &mut ExportContext<'tcx>,
) -> Value {
    let Some(required) = body.required_consts.as_ref() else {
        return unavailable_compiler_fact(
            "compiler body has no required_consts list; absence does not establish an empty list",
        );
    };
    let checks=required.iter().enumerate().map(|(index,operand)|{
        let environment=body.typing_env(tcx);
        let free_caller=already_instantiated && instance.def.has_polymorphic_mir_body()
            && (operand.const_.has_non_region_param() || operand.const_.has_escaping_bound_vars()
                || operand.const_.has_infer() || operand.const_.has_placeholders());
        let result=if free_caller {
            unavailable_compiler_fact("already substituted required constant retains caller parameters; complete caller environment required")
        }else{match instance.try_instantiate_mir_and_normalize_erasing_regions(tcx,environment,
                ty::EarlyBinder::bind(tcx,operand.const_)) {
            Err(error)=>json!({"status":"unsupported","kind":"required_const_normalization_error","error_debug":format!("{error:?}")}),
            Ok(normalized)=>{
                let mut normalized_operand=operand.clone(); normalized_operand.const_=normalized;
                match normalized.eval(tcx,environment,operand.span) {
                    Ok(value)=>json!({"status":"supported","normalized_operand":const_operand_json(context,tcx,body,&normalized_operand),
                        "value":const_value_json(context,tcx,normalized.ty(),value)}),
                    Err(error)=>json!({"status":"unsupported","kind":"required_const_evaluation_error","error_debug":format!("{error:?}")}),
                }
            }
        }};
        json!({"index":index,"span":span_json(tcx,operand.span),"result":result})
    }).collect::<Vec<_>>();
    json!({"status":"supported","typing_env":"body_typing_env","checks":checks})
}

// interpret/discriminant.rs and Ty::{discriminant_ty,discriminant_for_variant}.
fn discriminant_facts_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
) -> Value {
    use rustc_middle::ty::CoroutineArgsExt;
    let (values, count) = match input.kind() {
        ty::Adt(def, _) => {
            let values = if def.is_enum() {
                Some(def.discriminants(tcx).collect::<Vec<_>>())
            } else {
                None
            };
            (values, Some(def.variants().len()))
        }
        ty::Coroutine(def, args) => {
            if tcx.coroutine_layout(*def, args).is_err() {
                return unavailable_compiler_fact(
                    "compiler coroutine layout unavailable for discriminant range",
                );
            }
            (
                Some(
                    args.as_coroutine()
                        .discriminants(*def, tcx)
                        .collect::<Vec<_>>(),
                ),
                None,
            )
        }
        ty::UnsafeBinder(bound) => {
            return discriminant_facts_json(
                context,
                tcx,
                tcx.instantiate_bound_regions_with_erased((*bound).into()),
            );
        }
        _ => (None, None),
    };
    compiler_fact(
        json!({"has_discriminants":values.is_some(),"adt_variant_count":count,
        "values":values.unwrap_or_default().into_iter().map(|(index,discriminant)|json!({
            "variant":index.as_u32(),"type":type_json(context,tcx,discriminant.ty),
            "bits":discriminant.val.to_string()})).collect::<Vec<_>>()}),
    )
}

fn discriminant_type_fact_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
) -> Value {
    match input.kind() {
        ty::UnsafeBinder(bound) => {
            let inner = tcx.instantiate_bound_regions_with_erased((*bound).into());
            if inner.has_escaping_bound_vars() || inner.has_non_region_param() {
                return unavailable_compiler_fact(
                    "unsafe-binder discriminant query retains bound type/const variables",
                );
            }
            discriminant_type_fact_json(context, tcx, inner)
        }
        ty::Pat(base, _) => discriminant_type_fact_json(context, tcx, *base),
        _ => compiler_fact(type_json(context, tcx, input.discriminant_ty(tcx))),
    }
}

// interpret/traits.rs::get_vtable_ptr, before source salt/reservation effects.
fn compiler_vtable_metadata_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
    predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> Value {
    let predicate_json = predicates
        .iter()
        .map(|predicate| existential_predicate_json(context, tcx, predicate))
        .collect::<Vec<_>>();
    let principal = predicates
        .principal()
        .map(|principal| tcx.instantiate_bound_regions_with_erased(principal));
    let entries = if let Some(principal) = principal {
        tcx.vtable_entries(principal.with_self_ty(tcx, input))
    } else {
        TyCtxt::COMMON_VTABLE_ENTRIES
    };
    let entry_json=entries.iter().map(|entry|match *entry {
        ty::VtblEntry::MetadataDropInPlace=>if input.needs_drop(tcx,ty::TypingEnv::fully_monomorphized()) {
            let instance=ty::Instance::resolve_drop_glue(tcx,input);
            let instance_id=context.register_instance(instance);
            json!({"status":"supported","kind":"drop_in_place","instance_id":instance_id})
        }else{json!({"status":"supported","kind":"drop_in_place_null"})},
        ty::VtblEntry::MetadataSize=>json!({"status":"supported","kind":"size_bytes"}),
        ty::VtblEntry::MetadataAlign=>json!({"status":"supported","kind":"align_bytes"}),
        ty::VtblEntry::Vacant=>json!({"status":"supported","kind":"vacant"}),
        ty::VtblEntry::Method(instance)=>{
            let instance_id=context.register_instance(instance);
            json!({"status":"supported","kind":"method","instance_id":instance_id,
                "def_id":def_json(instance.def.def_id()),"def_path":tcx.def_path_str(instance.def.def_id()),
                "generic_args":generic_args_json(context,tcx,instance.args)})
        },
        ty::VtblEntry::TraitVPtr(trait_ref)=>{
            let existential=ty::ExistentialTraitRef::erase_self_ty(tcx,trait_ref);
            let allocation=tcx.vtable_allocation((input,Some(existential)));
            if let Some(GlobalAlloc::VTable(child_type,child_predicates))=tcx.try_get_global_alloc(allocation) {
                context.vtable_query_requests.insert((child_type,child_predicates));
            }
            json!({"status":"supported","kind":"supertrait_vtable_pointer",
                "trait_def_id":def_json(trait_ref.def_id),"trait_def_path":tcx.def_path_str(trait_ref.def_id),
                "generic_args":generic_args_json(context,tcx,trait_ref.args),
                "allocation":allocation_ref(context,tcx,allocation)})
        },
    }).collect::<Vec<_>>();
    let (size_bytes, align_bytes, layout_status) =
        match tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(input)) {
            Ok(layout) => (
                Some(layout.size.bytes()),
                Some(layout.align.abi.bytes()),
                "supported",
            ),
            Err(_) => (None, None, "unsupported"),
        };
    let status = if predicate_json
        .iter()
        .chain(entry_json.iter())
        .all(|value| value.get("status").and_then(Value::as_str) == Some("supported"))
        && layout_status == "supported"
    {
        "supported"
    } else {
        "unsupported"
    };
    json!({"status":status,"type":type_json(context,tcx,input),"size_bytes":size_bytes,"align_bytes":align_bytes,
        "layout_status":layout_status,"predicates":predicate_json,
        "principal_predicate":predicates.principal().map(|p|existential_predicate_json(context,tcx,p.map_bound(ty::ExistentialPredicate::Trait))),
        "entries":entry_json})
}

fn compiler_vtable_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> (Value, HashMap<(u64, Vec<u64>), u64>) {
    let mut allocations = context
        .allocation_ids
        .iter()
        .map(|(alloc, id)| (*id, *alloc))
        .collect::<Vec<_>>();
    allocations.sort_by_key(|(id, _)| *id);
    let mut pairs = context.vtable_query_requests.clone();
    for (_, alloc) in allocations {
        if let Some(GlobalAlloc::VTable(input, predicates)) = tcx.try_get_global_alloc(alloc) {
            pairs.insert((input, predicates));
        }
    }
    let mut processed = HashSet::new();
    let mut rows = Vec::new();
    loop {
        let mut pending = pairs.difference(&processed).copied().collect::<Vec<_>>();
        if pending.is_empty() {
            break;
        }
        // Seed any query-only identities in a deterministic compiler-type order
        // before assigning serialization-local IDs. HashSet iteration must never
        // decide either type IDs or the canonical query row order.
        pending.sort_by_key(|(input, predicates)| format!("{input:?}|{predicates:?}"));
        for (input, predicates) in pending {
            processed.insert((input, predicates));
            let input_json = type_json(context, tcx, input);
            let input_type_id = context.type_id(input);
            let mut input_predicates = Vec::new();
            let mut input_predicate_ids = Vec::new();
            for predicate in predicates.iter() {
                input_predicate_ids.push(context.predicate_id(predicate));
                input_predicates.push(existential_predicate_json(context, tcx, predicate));
            }
            let (output, erased) = tcx.erase_and_anonymize_regions((input, predicates));
            let output_json = type_json(context, tcx, output);
            let output_type_id = context.type_id(output);
            let output_predicates = erased
                .iter()
                .map(|p| existential_predicate_json(context, tcx, p))
                .collect::<Vec<_>>();
            let output_predicate_ids = erased
                .iter()
                .map(|p| context.predicate_id(p))
                .collect::<Vec<_>>();
            let ordering = (
                input_type_id,
                input_predicate_ids.clone(),
                output_type_id,
                output_predicate_ids,
            );
            let row = json!({"status":"supported","input_type":input_json,
            "input_predicates":input_predicates,
            "output_type":output_json,
            "output_predicates":output_predicates,
            "output_type_monomorphic_enough":!output.has_param(),
            "output_predicates_monomorphic_enough":!erased.has_param(),
            "vtable_metadata":compiler_vtable_metadata_json(context,tcx,input,predicates)});
            rows.push((ordering, (input_type_id, input_predicate_ids), row));
            pairs.extend(context.vtable_query_requests.iter().copied());
        }
    }
    rows.sort_by(|left, right| left.0.cmp(&right.0));
    let mut query_ids = HashMap::new();
    let records = rows
        .into_iter()
        .enumerate()
        .map(|(query_id, (_, key, mut row))| {
            query_ids.insert(key, query_id as u64);
            row["query_id"] = json!(query_id);
            row
        })
        .collect::<Vec<_>>();
    (Value::Array(records), query_ids)
}

fn patch_vtable_query_ids(document: &mut Value, query_ids: &HashMap<(u64, Vec<u64>), u64>) {
    match document {
        Value::Array(values) => {
            for value in values {
                patch_vtable_query_ids(value, query_ids);
            }
        }
        Value::Object(fields) => {
            let unresolved = if let Some(query) = fields.get_mut("vtable_query") {
                if !query.is_null() {
                    let key = query.get("_query_key").and_then(|key| {
                        let input = key.get("input_type_id")?.as_u64()?;
                        let predicates = key
                            .get("input_predicate_ids")?
                            .as_array()?
                            .iter()
                            .map(Value::as_u64)
                            .collect::<Option<Vec<_>>>()?;
                        Some((input, predicates))
                    });
                    if let Some(id) = key.and_then(|key| query_ids.get(&key).copied()) {
                        if let Some(object) = query.as_object_mut() {
                            object.insert("query_id".into(), json!(id));
                            object.remove("_query_key");
                        }
                        false
                    } else {
                        if let Some(object) = query.as_object_mut() {
                            object.insert("status".into(), json!("unknown"));
                            object.insert("reason".into(),json!("Cast vtable query pair was absent from the finalized exact compiler query catalog"));
                            object.remove("_query_key");
                        }
                        true
                    }
                } else {
                    false
                }
            } else {
                false
            };
            if unresolved {
                fields.insert("status".into(), json!("unknown"));
            }
            for value in fields.values_mut() {
                patch_vtable_query_ids(value, query_ids);
            }
        }
        _ => (),
    }
}

// Link each abstract virtual call identity only to exact compiler query rows
// produced for that same virtual Instance. The catalog may contain many
// unrelated concrete vtables; those rows are not dispatch evidence for this
// call and must not be attached by type coincidence.
fn patch_virtual_resolution_candidates(document: &mut Value) {
    let mut candidates: HashMap<u64, Vec<u64>> = HashMap::new();
    if let Some(rows) = document
        .pointer("/compiler_runtime_queries/virtual")
        .and_then(Value::as_array)
    {
        for row in rows {
            let Some(instance_id) = row.get("original_instance_id").and_then(Value::as_u64) else {
                continue;
            };
            let Some(query_id) = row
                .pointer("/vtable_query/query_id")
                .and_then(Value::as_u64)
            else {
                continue;
            };
            candidates.entry(instance_id).or_default().push(query_id);
        }
    }
    for ids in candidates.values_mut() {
        ids.sort_unstable();
        ids.dedup();
    }
    fn patch(value: &mut Value, candidates: &HashMap<u64, Vec<u64>>) {
        match value {
            Value::Object(fields) => {
                if let Some(resolution) = fields
                    .get_mut("virtual_resolution")
                    .filter(|value| !value.is_null())
                {
                    if let Some(instance_id) = resolution.get("instance_id").and_then(Value::as_u64)
                    {
                        if let Some(object) = resolution.as_object_mut() {
                            object.insert(
                                "candidate_query_ids".into(),
                                json!(candidates.get(&instance_id).cloned().unwrap_or_default()),
                            );
                        }
                    }
                }
                for child in fields.values_mut() {
                    patch(child, candidates)
                }
            }
            Value::Array(values) => {
                for child in values {
                    patch(child, candidates)
                }
            }
            _ => (),
        }
    }
    patch(document, &candidates);
}

fn intrinsic_fallback_is_spec(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> bool {
    tcx.get_attrs_by_path(
        def,
        &[
            rustc_span::sym::miri,
            rustc_span::Symbol::intern("intrinsic_fallback_is_spec"),
        ],
    )
    .next()
    .is_some()
}
fn intrinsic_metadata_json(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> Value {
    if !matches!(
        tcx.def_kind(def),
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
    ) {
        return unavailable_compiler_fact("intrinsic query requires a function definition");
    }
    compiler_fact(match tcx.intrinsic(def) {
        Some(info) => json!({"must_be_overridden":info.must_be_overridden,
            "fallback_is_spec":intrinsic_fallback_is_spec(tcx,def)}),
        None => Value::Null,
    })
}

// step.rs::eval_fn_call: normalized original signature for arity/ExternAbi,
// original FnPtr binder plus exact ordered extra argument types for FnAbi.
fn compiler_function_facts_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Value {
    // Serializing a function signature recursively serializes its input and
    // output types. Those can themselves contain function items/pointers, so
    // walk the interned type set to a fixed point instead of snapshotting one
    // possibly incomplete prefix.
    for (input, extra) in context.fn_pointer_abi_requests.clone() {
        context.type_id(input);
        for ty in extra.iter() {
            context.type_id(ty);
        }
    }
    let mut types = BTreeMap::<u64, ty::Ty<'tcx>>::new();
    let mut records = BTreeMap::<u64, Value>::new();
    loop {
        let mut pending = context
            .type_ids
            .iter()
            .filter(|(input, id)| {
                matches!(input.kind(), ty::FnDef(..) | ty::FnPtr(..))
                    && !types.contains_key(id)
            })
            .map(|(input, id)| (*id, *input))
            .collect::<Vec<_>>();
        pending.sort_by_key(|(id, _)| *id);
        if pending.is_empty() {
            break;
        }
        for (id, input) in pending {
            types.insert(id, input);
            let closed=!input.has_non_region_param() && !input.has_escaping_bound_vars() && !input.has_infer() && !input.has_placeholders();
            let signature=if !closed {unavailable_compiler_fact("function signature requires a complete monomorphic type")}
            else{match tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(),ty::Unnormalized::new_wip(input.fn_sig(tcx))){
                Ok(sig)=>compiler_fact(fn_sig_json_inner(context,tcx,tcx.instantiate_bound_regions_with_erased(sig))),
                Err(error)=>json!({"status":"unsupported","reason":"function signature normalization failed","error_debug":format!("{error:?}")}),
            }};
            let kind=match *input.kind(){
                ty::FnPtr(..)=>json!({"kind":"function_pointer"}),
                ty::FnDef(def,args)=>json!({"kind":"function_definition","instance_kind":instance_kind_json(context,tcx,ty::InstanceKind::Item(def)),"generic_args":generic_args_json(context,tcx,args.skip_binder())}),
                _=>unreachable!(),
            };
            records.insert(id, json!({"type_id":id,"typing_env":"fully_monomorphized","function_kind":kind,"signature_query":signature}));
        }
    }
    let helper_inputs = types.iter().map(|(id, input)| (*id, *input)).collect::<Vec<_>>();
    let known_function_type_ids = types.keys().copied().collect::<HashSet<_>>();
    let records = records.into_values().collect::<Vec<_>>();
    let mut requests = context.fn_pointer_abi_requests.clone();
    for (_, input) in types {
        if matches!(input.kind(), ty::FnPtr(..)) {
            requests.insert((input, ty::List::empty()));
        }
    }
    let mut requests = requests.into_iter().collect::<Vec<_>>();
    requests.sort_by_key(|(ty, extra)| {
        (
            context.type_id(*ty),
            extra
                .iter()
                .map(|ty| context.type_id(ty))
                .collect::<Vec<_>>(),
        )
    });
    let abis=requests.into_iter().map(|(input,extra)|{
        let closed=!input.has_non_region_param() && !input.has_escaping_bound_vars() && !input.has_infer() && !input.has_placeholders()
            && !extra.has_non_region_param() && !extra.has_escaping_bound_vars() && !extra.has_infer() && !extra.has_placeholders();
        let abi=if !closed {unavailable_compiler_fact("FnPtr ABI requires a complete monomorphic function type and extra argument vector")}
        else{match tcx.fn_abi_of_fn_ptr(ty::TypingEnv::fully_monomorphized().as_query_input((input.fn_sig(tcx),extra))){
            Ok(abi)=>compiler_fact(fn_abi_json(context,tcx,abi)),
            Err(error)=>json!({"status":"unsupported","reason":"rustc fn_abi_of_fn_ptr failed","error_debug":format!("{error:?}")}),
        }};
        json!({"type_id":context.type_id(input),"typing_env":"fully_monomorphized",
            "extra_argument_types":extra.iter().map(|ty|type_json(context,tcx,ty)).collect::<Vec<_>>(),"abi_query":abi})
    }).collect::<Vec<_>>();
    // helpers.rs::call_function constructs a Safe, nonvariadic, unsplatted
    // dummy-binder signature from actual argument/output types. Query exact
    // constructor candidates; adapters must match every request field.
    let mut helper_signatures = Vec::new();
    let mut seen = HashSet::new();
    for (_, input) in helper_inputs {
        if input.has_non_region_param()
            || input.has_escaping_bound_vars()
            || input.has_infer()
            || input.has_placeholders()
        {
            continue;
        }
        let Ok(bound) = tcx.try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            ty::Unnormalized::new_wip(input.fn_sig(tcx)),
        ) else {
            continue;
        };
        let original = tcx.instantiate_bound_regions_with_erased(bound);
        for output in [original.output(), tcx.types.unit] {
            for abi in [original.abi(), rustc_abi::ExternAbi::Rust] {
                for caller_location in [false, true] {
                    if caller_location
                        && tcx
                            .lang_items()
                            .get(rustc_attr_ir::LangItem::PanicLocation)
                            .is_none()
                    {
                        continue;
                    }
                    // RustCall keeps its tupled argument as the final input;
                    // adding the caller-location ABI parameter would make the
                    // compiler query invalid before it could return an error.
                    if caller_location && abi == rustc_abi::ExternAbi::RustCall {
                        continue;
                    }
                    let inputs = original
                        .inputs()
                        .iter()
                        .copied()
                        .chain(caller_location.then(|| tcx.caller_location_ty()));
                    let signature = tcx.mk_fn_sig(
                        inputs,
                        output,
                        ty::FnSigKind::default()
                            .set_abi(abi)
                            .set_safety(rustc_hir::Safety::Safe),
                    );
                    if !seen.insert(signature) {
                        continue;
                    }
                    let result = match tcx.fn_abi_of_fn_ptr(
                        ty::TypingEnv::fully_monomorphized()
                            .as_query_input((ty::Binder::dummy(signature), ty::List::empty())),
                    ) {
                        Ok(abi) => compiler_fact(fn_abi_json(context, tcx, abi)),
                        Err(error) => {
                            json!({"status":"unsupported","reason":"helper dummy signature ABI query failed","error_debug":format!("{error:?}")})
                        }
                    };
                    helper_signatures.push(json!({"typing_env":"fully_monomorphized","signature":fn_sig_json_inner(context,tcx,signature),"splatted":false,"abi_query":result}));
                }
            }
        }
    }
    // ABI projection and the candidate helper-signature queries also pass
    // their exact compiler parameter types through type_json. If either query
    // registered another function type, close over it and rebuild this catalog
    // so the emitted table still covers the complete referenced type set.
    if context.type_ids.iter().any(|(input, id)| {
        matches!(input.kind(), ty::FnDef(..) | ty::FnPtr(..))
            && !known_function_type_ids.contains(id)
    }) {
        return compiler_function_facts_json(tcx, context);
    }
    json!({"types":records,"pointer_abis":abis,"helper_signatures":helper_signatures})
}
