#![feature(rustc_private)]

mod incremental;
mod cast_queries;
mod allocator_world;
mod covariance_queries;
mod foreign_symbols;
mod generated_call_queries;
mod global_byte_queries;
mod intrinsic_symbol_queries;
mod intrinsic_value_queries;
mod libc_type_layouts;
mod main_queries;
mod named_constants;
mod named_statics;
mod native_signature_queries;
mod typed_pool;
mod pool_type;
mod pool_layout;
mod pool_instance;
mod pool_values;
mod pool_constant;
mod pool_body;
mod allocation_values;
mod resolution_values;
mod panic_queries;
mod producer;
#[cfg(feature = "miri-reference")]
mod reference_values;
#[cfg(feature = "miri-reference")]
mod reference_ui;
mod projection_queries;
mod retag_queries;
mod shim_abi;
mod startup_queries;
mod vtable_diagnostics;
mod query_values;
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
use typed_pool::{OrderedSet, Pool};
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::io::Write;
#[cfg(feature = "miri-reference")]
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface;
use rustc_middle::mir::interpret::{AllocId, CTFE_ALLOC_SALT, GlobalAlloc};
use rustc_middle::ty::{self, ExistentialPredicateStableCmpExt, TyCtxt, TypeVisitableExt};
use rustc_span::Pos;

/// An unavailable semantic fact aborts the complete export, never a payload row.
fn export_failure<T>(context: &str, details: impl std::fmt::Display) -> Result<T, String> {
    Err(format!("{context}: {details}"))
}

const EXPECTED_RUSTC_COMMIT: &str = "8144389c895da997dbdecaa635e41d6a50be6ffd";
const MIRI_COMMIT: &str = "7fa591d7d4dd9af8154becbc8332f8096f8323b1";
const ROOT_SCHEMA_VERSION: u64 = 7;

struct Options {
    output: PathBuf,
    rustc_args: Vec<String>,
    root_paths: Vec<String>,
}

#[derive(serde::Serialize)]
struct Producer {
    miri_commit: &'static str,
    rustc_commit: &'static str,
    rustc_version: String,
    target_triple: String,
    input_settings: producer::Evidence,
}
#[derive(serde::Serialize)]
struct SessionQueries {
    internal_target_features: Vec<String>,
    is_like_wasm: bool,
    target_arch: String,
    root_span: u64,
    runtime_checks: [pool_body::RuntimeCheck; 3],
}
#[derive(serde::Serialize)]
struct RuntimeQueries {
    #[serde(skip_serializing_if = "Option::is_none")]
    startup: Option<startup_queries::Catalog>,
    types: Vec<query_values::RuntimeTypeQuery>,
    #[serde(rename = "virtual")]
    virtual_queries: Vec<query_values::RuntimeVirtualQuery<query_values::VtableRef>>,
    instances: Vec<CallerInstance>,
    foreign_symbols: foreign_symbols::Catalog,
}
#[derive(serde::Serialize)]
struct SelectedRoot {
    def_path: String,
    def_id: u64,
}
#[derive(serde::Serialize)]
struct SelectedScope {
    kind: &'static str,
    semantics: &'static str,
    roots: Vec<SelectedRoot>,
    dependency_policy: &'static str,
}
#[derive(serde::Serialize)]
struct PromotedRoot {
    promoted_index: u32,
    body: u64,
}
#[derive(serde::Serialize)]
struct BodyRoot {
    body: u64,
    entry_instance: u64,
    def_path: String,
    def_id: u64,
    is_static: bool,
    thread_local_static: bool,
    promoted_bodies: Vec<PromotedRoot>,
}
/// Owned, closed export graph. Pending reference types cannot inhabit this snapshot.
#[derive(serde::Serialize)]
struct ExportDocument {
    schema: &'static str,
    schema_version: u64,
    mir_query: &'static str,
    compiler_abi_layout_schema: &'static str,
    producer: Producer,
    runtime_target_data_layout: producer::TargetDataLayout,
    compiler_session_queries: SessionQueries,
    compiler_runtime_queries: RuntimeQueries,
    compiler_frame_metadata: FrameMetadata,
    compiler_instance_abis: Vec<InstanceAbi>,
    compiler_function_facts: FunctionFacts,
    compiler_cast_queries: Vec<cast_queries::Query>,
    compiler_type_name_constants: Vec<intrinsic_value_queries::TypeName>,
    compiler_panic_queries: Vec<panic_queries::Query>,
    compiler_native_signature_queries: Vec<native_signature_queries::Query>,
    compiler_retag_queries: Vec<retag_queries::Query>,
    compiler_covariance_queries: Vec<covariance_queries::Query>,
    compiler_global_byte_queries: global_byte_queries::Queries,
    compiler_caller_location_constants: Vec<intrinsic_value_queries::CallerLocation>,
    compiler_main_queries: main_queries::Catalog,
    compiler_runtime_primitives: RuntimePrimitives,
    compiler_vtable_queries: Vec<query_values::VtableQuery>,
    compiler_predicate_queries: Vec<query_values::PredicateQuery>,
    #[serde(flatten)]
    runtime_catalogs: RuntimeCatalogs,
    body_roots: Vec<BodyRoot>,
    bodies: Vec<pool_body::Body<u64, Vec<u64>>>,
    definitions: Vec<pool_values::Definition>,
    type_constants: Vec<pool_values::TypeConstant>,
    files: Vec<String>,
    spans: Vec<pool_values::Span>,
    layouts: Vec<pool_layout::Layout>,
    fn_abis: Vec<pool_layout::FnAbi>,
    instances: Vec<pool_instance::Instance>,
    types: Vec<pool_type::Type>,
    byte_images: Vec<String>,
    allocations: Vec<allocation_values::Entry>,
    predicates: Vec<allocation_values::Predicate>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_alloc_id_world: Option<allocator_world::World>,
    #[serde(skip_serializing_if = "Option::is_none")]
    selected_scope: Option<SelectedScope>,
    #[serde(skip_serializing_if = "Option::is_none")]
    invocation: Option<Invocation>,
}

#[derive(serde::Serialize)]
#[serde(tag = "kind")]
enum Invocation {
    #[serde(rename = "direct_rustc_driver")]
    Direct {
        rustc_commit: &'static str,
        rustc_executable: Option<String>,
        working_directory: Option<String>,
        rustc_args: Vec<String>,
        rustc_args_fingerprint_fnv1a64: String,
        root_paths: Vec<String>,
    },
    #[serde(rename = "cargo_rustc_wrapper")]
    Cargo {
        rustc_commit: &'static str,
        rustc_executable: String,
        working_directory: Option<String>,
        crate_name: String,
        source_path: Option<String>,
        target_crate: bool,
        rustc_args: Vec<String>,
        rustc_args_fingerprint_fnv1a64: String,
    },
}
impl Invocation {
    fn rustc_args(&self) -> &[String] {
        match self {
            Self::Direct { rustc_args, .. } | Self::Cargo { rustc_args, .. } => rustc_args,
        }
    }
}

struct ExportCallbacks {
    output: PathBuf,
    root_paths: Vec<String>,
    rustc_version: String,
    document: Option<ExportDocument>,
    diagnostics: Option<(PathBuf, vtable_diagnostics::Report)>,
    invocation: Option<Invocation>,
    write_during_analysis: bool,
    continue_compilation: bool,
    prepared_allocator_world: bool,
    miri_reference: bool,
    #[cfg(feature = "miri-reference")]
    miri_reference_args: Vec<String>,
    export_error: Option<String>,
}

/// Compilation-scoped identities for the actual interned rustc types.
/// The numeric IDs are serialization-local and deliberately carry no claim of
/// cross-compilation stability. Type graph nodes live in `type_ids`; MIR
/// payloads refer to them by `type_id`.
#[derive(Default)]
struct ExportContext<'tcx> {
    reachable_instance_cursor: usize,
    backtrace_event_cursor: usize,
    backtrace_frame_cursor: usize,
    backtrace_demanded: bool,
    runtime_type_cursor: usize,
    runtime_type_deferred: Vec<ty::Ty<'tcx>>,
    catch_unwind_frontier: incremental::PairFrontier,
    /// Fresh identities and membership changes wake consumers whose eligibility
    /// depends on metadata-only or runtime-only status. Unchanged registration
    /// emits no event, so completed ABI and allocator requests stay completed.
    instance_events: Vec<ty::Instance<'tcx>>,
    covariance_pair_cursor: usize,
    covariance_vtable_cursor: usize,
    covariance_pairs: OrderedSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    cast_state: incremental::Casts<'tcx>,
    abi_state: incremental::Abis<'tcx>,
    vtable_state: incremental::Vtables,
    virtual_state: incremental::Virtuals<'tcx>,
    vtable_diagnostics: vtable_diagnostics::Trace<'tcx>,
    bodies: Pool<BodyKey<'tcx>, pool_body::Body>,
    definitions: Pool<rustc_hir::def_id::DefId, pool_values::Definition>,
    type_constants: Pool<ty::Const<'tcx>, pool_values::TypeConstant>,
    files: pool_values::Files,
    spans: Pool<rustc_span::Span, pool_values::Span>,
    layouts: Pool<rustc_abi::TyAndLayout<'tcx, ty::Ty<'tcx>>, pool_layout::Layout>,
    fn_abis: Pool<rustc_target::callconv::FnAbi<'tcx, ty::Ty<'tcx>>, pool_layout::FnAbi>,
    type_ids: Pool<rustc_middle::ty::Ty<'tcx>, pool_type::Type>,
    /// Types demanded by serialized source MIR/signatures/metadata. Compiler
    /// query constructors can create type nodes without adding them here.
    runtime_type_query_demands: OrderedSet<rustc_middle::ty::Ty<'tcx>>,
    runtime_type_query_suppression: usize,
    type_nodes_in_progress: HashSet<rustc_middle::ty::Ty<'tcx>>,
    byte_images: allocation_values::ByteImages,
    allocation_ids: Pool<AllocId, allocation_values::Allocation>,
    allocations_in_progress: HashSet<AllocId>,
    instance_ids: Pool<ty::Instance<'tcx>, pool_instance::Instance>,
    /// DropGlue(None) identities first discovered as runtime type-query facts
    /// have no operation and should not seed ABI/MIR query closure by themselves.
    /// A real source use upgrades them in `register_instance`.
    runtime_query_only_empty_drops: HashSet<ty::Instance<'tcx>>,
    /// Net membership changes in the current catalog fixpoint round.
    identity_membership_delta:
        HashSet<(IdentityMembershipSet, ty::Instance<'tcx>)>,
    /// Instances discovered only while reproducing symbol lookup need their
    /// mono identity, but not the unrelated caller-location/target-feature
    /// query family. Remove them when a real MIR demand upgrades the entry.
    symbol_only_instances: HashSet<ty::Instance<'tcx>>,
    // Metadata references must not seed runtime compiler-query demands.
    metadata_only_instances: HashSet<ty::Instance<'tcx>>,
    pending_instances: Vec<ty::Instance<'tcx>>,
    emitted_instances: HashSet<ty::Instance<'tcx>>,
    predicate_ids: Pool<ty::PolyExistentialPredicate<'tcx>, allocation_values::Predicate>,
    predicates_in_progress: HashSet<ty::PolyExistentialPredicate<'tcx>>,
    pending_predicates: Vec<ty::PolyExistentialPredicate<'tcx>>,
    instance_abi_requests: OrderedSet<(ty::Instance<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
    caller_location_span_set: HashSet<rustc_span::Span>,
    caller_location_spans: Vec<rustc_span::Span>,
    /// Caller-location construction is a rustc hook, not a memoized query;
    /// each invocation allocates a fresh global. Cache the exact serialized
    /// result once per source span so closure rounds do not invent identities.
    caller_location_constant_rows: HashMap<rustc_span::Span, intrinsic_value_queries::CallerLocationFact>,
    cast_unsize_requests: OrderedSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    vtable_query_requests: OrderedSet<(
        ty::Ty<'tcx>,
        &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    )>,
    /// Dynamic-to-dynamic casts construct a destination vtable for the
    /// concrete type carried by the source vtable. Keep the exact lockstep
    /// dynamic tails so compiler_vtable_queries_json can close those demands
    /// over source vtables discovered from MIR and globals.
    dynamic_vtable_upcast_requests: OrderedSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    /// Exact type pairs which Miri's transmute/subtype cast path passes to
    /// rustc's `mir_assign_valid_types`, even when their normalized types do
    /// not share the finite identity-group query domain.
    covariance_query_requests: OrderedSet<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    cast_box_requests: OrderedSet<ty::Ty<'tcx>>,
    fn_pointer_abi_requests: OrderedSet<(ty::Ty<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
    /// Concrete candidates produced by function allocations referenced in
    /// compiler constants or by resolved function-pointer casts present in
    /// actual MIR. This is not a flow-sensitive points-to set.
    fn_pointer_targets: OrderedSet<ty::Instance<'tcx>>,
    /// Instances with source MIR bodies that this exporter emitted. Miri's
    /// backtrace shims turn active frame instances into function pointers even
    /// when MIR contains no corresponding reification cast.
    runtime_mir_frame_instances: OrderedSet<ty::Instance<'tcx>>,
    /// Types used as the source of actual MIR ReifyFnPointer or
    /// ClosureFnPointer casts. `cast_queries` resolves all demanded function
    /// types, but only these source casts add their result as a candidate.
    fn_pointer_cast_inputs: OrderedSet<ty::Ty<'tcx>>,
    fn_pointer_call_transfers: Vec<CallTransferRequest<'tcx>>,
    /// Reached foreign calls can delegate to an exact exported-symbol winner.
    /// Keep their actual operands until symbol discovery selects that body.
    foreign_call_transfers: Vec<(ty::Instance<'tcx>, CallTransferRequest<'tcx>, bool)>,
    foreign_call_transfer_keys: HashSet<(ty::Instance<'tcx>, CallTransferRequest<'tcx>, bool)>,
    processed_foreign_transfers: HashSet<(usize, ty::Instance<'tcx>)>,
    runtime_callback_transfers: Vec<RuntimeCallbackTransferRequest<'tcx>>,
    runtime_callback_transfer_keys: HashSet<(String, ty::Ty<'tcx>, Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>)>,
    processed_runtime_callback_transfers: incremental::PairFrontier,
    /// Exact source argument types for intrinsic catch_unwind calls whose
    /// helper-internal callbacks have no MIR Call terminator.
    runtime_catch_unwind_sites: OrderedSet<(ty::Ty<'tcx>, ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    /// Payload argument types reaching Miri's panic-start shim and later
    /// forwarded to the catch_unwind callback.
    runtime_unwind_payload_types: OrderedSet<ty::Ty<'tcx>>,
    virtual_call_transfers: Vec<(ty::Instance<'tcx>, CallTransferRequest<'tcx>)>,
    processed_fn_pointer_transfers: incremental::PairFrontier,
    processed_virtual_transfers: HashSet<(usize, ty::Instance<'tcx>)>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct CallTransferRequest<'tcx> {
    function_ty: ty::Ty<'tcx>,
    caller_env: ty::TypingEnv<'tcx>,
    caller_instance: Option<ty::Instance<'tcx>>,
    caller_args: Vec<ty::Ty<'tcx>>,
    extra_types: &'tcx ty::List<ty::Ty<'tcx>>,
    return_destination: ty::Ty<'tcx>,
    /// Miri creates this call outside guest MIR. Preserve its actual ABI
    /// (Rust, C, System, ...) when constructing the caller FnPtr signature.
    generated_caller_abi: Option<rustc_abi::ExternAbi>,
}

#[derive(Clone)]
struct RuntimeCallbackTransferRequest<'tcx> {
    source_symbol: String,
    callback_operand_type: ty::Ty<'tcx>,
    request: CallTransferRequest<'tcx>,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct BodyKey<'tcx> {
    instance: ty::Instance<'tcx>,
    promoted: Option<rustc_middle::mir::Promoted>,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
enum IdentityMembershipSet {
    MetadataOnly,
    SymbolOnly,
    RuntimeQueryOnlyEmptyDrop,
}

impl<'tcx> ExportContext<'tcx> {
    fn note_identity_membership_change(
        &mut self,
        set: IdentityMembershipSet,
        instance: ty::Instance<'tcx>,
    ) {
        self.instance_events.push(instance);
        let key = (set, instance);
        if !self.identity_membership_delta.remove(&key) {
            self.identity_membership_delta.insert(key);
        }
    }

    fn predicate_id(&mut self, predicate: ty::PolyExistentialPredicate<'tcx>) -> u64 {
        let (id, fresh) = self.predicate_ids.reserve(predicate);
        if fresh {
            self.pending_predicates.push(predicate);
        }
        id as u64
    }
    fn type_id(&mut self, ty: rustc_middle::ty::Ty<'tcx>) -> u64 {
        self.type_ids.reserve(ty).0 as u64
    }

    fn allocation_id(&mut self, alloc_id: AllocId) -> u64 {
        self.allocation_ids.reserve(alloc_id).0 as u64
    }

    fn register_instance(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        if self.metadata_only_instances.remove(&instance) {
            self.note_identity_membership_change(IdentityMembershipSet::MetadataOnly, instance);
        }
        if self.runtime_query_only_empty_drops.remove(&instance) {
            self.note_identity_membership_change(
                IdentityMembershipSet::RuntimeQueryOnlyEmptyDrop,
                instance,
            );
        }
        if self.symbol_only_instances.remove(&instance) {
            self.note_identity_membership_change(IdentityMembershipSet::SymbolOnly, instance);
        }
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
        let (id, _) = self.reserve_instance_identity(instance);
        self.pending_instances.push(instance);
        id as u64
    }

    fn reserve_instance_identity(&mut self, instance: ty::Instance<'tcx>) -> (u64, bool) {
        let (id, fresh) = self.instance_ids.reserve(instance);
        if fresh { self.instance_events.push(instance); }
        (id as u64, fresh)
    }

    /// Register compiler identity without eagerly querying MIR. Miri resolves
    /// exported-symbol identities during lookup and only calls `load_mir` for
    /// the selected function. Some rustc symbols have no MIR (and querying
    /// them eagerly can ICE), so callers must request a body separately.
    fn register_instance_identity(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        // Symbol lookup demands compiler queries even when metadata reserved the ID first.
        if self.metadata_only_instances.remove(&instance) {
            self.note_identity_membership_change(IdentityMembershipSet::MetadataOnly, instance);
        }
        let (id, fresh) = self.reserve_instance_identity(instance);
        if fresh && self.symbol_only_instances.insert(instance) {
            self.note_identity_membership_change(IdentityMembershipSet::SymbolOnly, instance);
        }
        id
    }

    fn register_metadata_instance(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        let (id, fresh) = self.reserve_instance_identity(instance);
        if fresh {
            self.metadata_only_instances.insert(instance);
            self.note_identity_membership_change(IdentityMembershipSet::MetadataOnly, instance);
            self.symbol_only_instances.insert(instance);
            self.note_identity_membership_change(IdentityMembershipSet::SymbolOnly, instance);
        }
        id
    }

    /// A real vtable method or concrete drop entry is a possible concrete
    /// target of Miri's virtual/drop path. The call path computes its own
    /// `FnAbi` and loads the resolved instance MIR, so preserve the ordinary
    /// instance/body closure and empty-extra-argument source query.
    fn register_vtable_target(&mut self, instance: ty::Instance<'tcx>) -> u64 {
        let id = self.register_instance(instance);
        self.instance_abi_requests
            .insert((instance, ty::List::empty()));
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
                "Usage:\n  lean-miri-mir-exporter --output FILE [--root DEF-PATH]... [--] RUSTC-ARG...\n  lean-miri-mir-exporter --cargo CARGO-ARGS...\n\nDirect mode exports typed MIR and stops after analysis. Optional --root selects exact non-generic local def-path roots and emits their reachable structural closure. Cargo mode acts as a rustc wrapper, writes one JSON file per compiled crate, and continues normal codegen/metadata emission. Set LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 to opt into a post-export raw allocation-world snapshot. Both require the pinned rustc revision."
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

fn prepared_allocator_world_enabled() -> Result<bool, String> {
    match env::var("LEAN_MIRI_PREPARED_ALLOC_ID_WORLD") {
        Ok(value) if value == "1" => Ok(true),
        Ok(value) if value == "0" || value.is_empty() => Ok(false),
        Ok(_) => Err("LEAN_MIRI_PREPARED_ALLOC_ID_WORLD must be 0 or 1".into()),
        Err(env::VarError::NotPresent) => Ok(false),
        Err(error) => Err(format!("cannot read prepared allocator-world opt-in: {error}")),
    }
}

fn prepared_miri_reference_enabled() -> Result<bool, String> {
    let enabled = match env::var("LEAN_MIRI_RUN_PREPARED_MIRI") {
        Ok(value) if value == "1" => true,
        Ok(value) if value == "0" || value.is_empty() => false,
        Ok(_) => return Err("LEAN_MIRI_RUN_PREPARED_MIRI must be 0 or 1".into()),
        Err(env::VarError::NotPresent) => false,
        Err(error) => return Err(format!("cannot read prepared Miri opt-in: {error}")),
    };
    if enabled && !cfg!(feature = "miri-reference") {
        return Err(
            "prepared Miri reference requires rebuilding exporter with --features miri-reference"
                .into(),
        );
    }
    Ok(enabled)
}

#[cfg(feature = "miri-reference")]
fn prepared_miri_reference_arguments() -> Result<Vec<String>, String> {
    match env::var("LEAN_MIRI_REFERENCE_ARGS_JSON") {
        Ok(value) => serde_json::from_str::<Vec<String>>(&value)
            .map_err(|error| format!("invalid LEAN_MIRI_REFERENCE_ARGS_JSON: {error}")),
        Err(env::VarError::NotPresent) => Ok(Vec::new()),
        Err(error) => Err(format!("cannot read prepared Miri arguments: {error}")),
    }
}

#[cfg(feature = "miri-reference")]
fn run_prepared_miri_reference_entry(
    tcx: TyCtxt<'_>,
    entry: rustc_hir::def_id::DefId,
    entry_type: miri::MiriEntryFnType,
    extra_args: &[String],
) -> reference_values::Result {
    use reference_values::{Config, TreeBorrows, Result as R, Status as S, Outcome as O};
    let mut config = miri::MiriConfig::default();
    config.borrow_tracker = Some(miri::BorrowTrackerMethod::TreeBorrows(
        miri::TreeBorrowsParams {
            precise_interior_mut: true,
            implicit_writes: false,
        },
    ));
    let empty_environment = match reference_ui::configure(&mut config) {
        Ok(empty) => empty,
        Err(reason) => return R::InvalidProfile { status: S::Failed, reason, outcome: O::InvalidUiProfile },
    };
    let file_name = tcx.sess.io.input.file_name(tcx.sess);
    let mut args = vec![file_name.prefer_local_unconditionally().to_string()];
    args.extend_from_slice(extra_args);
    config.args = args.clone();
    config.current_exe = file_name
        .into_local_path()
        .and_then(|path| path.canonicalize().ok());

    let (borrow_tracker, tree_borrows) = match &config.borrow_tracker {
        Some(miri::BorrowTrackerMethod::TreeBorrows(params)) => ("tree_borrows", Some(TreeBorrows {
            precise_interior_mut: params.precise_interior_mut, implicit_writes: params.implicit_writes })),
        None => ("none", None),
        Some(_) => ("unsupported", None),
    };
    let config_description = Config {
        same_tcx: true,
        borrow_tracker,
        tree_borrows,
        validation: format!("{:?}",config.validation),
        alignment_check: format!("{:?}",config.check_alignment),
        isolated_op: format!("{:?}",config.isolated_op),
        ignore_leaks: config.ignore_leaks,
        provenance_mode: format!("{:?}",config.provenance_mode),
        rng_seed: config.seed,
        data_race_detector: config.data_race_detector,
        weak_memory_emulation: config.weak_memory_emulation,
        track_outdated_loads: config.track_outdated_loads,
        genmc: config.genmc_config.is_some(),
        native_libraries: config.native_lib.len(),
        cmpxchg_weak_failure_rate: config.cmpxchg_weak_failure_rate,
        preemption_rate: config.preemption_rate,
        backtrace_style: format!("{:?}",config.backtrace_style),
        mute_stdout_stderr: config.mute_stdout_stderr,
        num_cpus: config.num_cpus,
        address_reuse_rate: config.address_reuse_rate,
        address_reuse_cross_thread_rate: config.address_reuse_cross_thread_rate,
        fixed_scheduling: config.fixed_scheduling,
        float_nondeterminism: config.float_nondet,
        float_rounding_error_mode: format!("{:?}",config.float_rounding_error),
        short_fd_operations: config.short_fd_operations,
        collect_leak_backtraces: config.collect_leak_backtraces,
        environment_policy: if empty_environment { "empty" } else { "host snapshot used; variable names and values are not serialized" },
        args: args,
    };
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        miri::eval_entry(tcx, entry, entry_type, &config, None)
    }));
    match outcome {
        Ok(Ok(())) => R::Executed { status: S::Completed, config: config_description, outcome: O::ExitZero },
        Ok(Err(code)) if tcx.dcx().has_errors().is_some() => R::Executed {
            status: S::Failed, config: config_description, outcome: O::MiriEvaluationError { exit_code: code.get() },
        },
        Ok(Err(code)) => R::Executed { status: S::Completed, config: config_description,
            outcome: O::GuestNonzeroExit { exit_code: code.get() } },
        Err(_) => R::Executed { status: S::Failed, config: config_description, outcome: O::MiriPanicked },
    }
}

#[cfg(feature = "miri-reference")]
fn reference_sidecar_path(snapshot: &Path) -> PathBuf {
    let mut path = snapshot.as_os_str().to_os_string();
    path.push(".miri-reference.json");
    PathBuf::from(path)
}

#[cfg(feature = "miri-reference")]
fn snapshot_fingerprint(path: &Path) -> Result<(String, u64), String> {
    let mut file = fs::File::open(path)
        .map_err(|error| format!("cannot read staged snapshot {}: {error}", path.display()))?;
    let mut buffer = [0u8; 64 * 1024];
    let mut hash = 0xcbf29ce484222325u64;
    let mut byte_length = 0u64;
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|error| format!("cannot read staged snapshot {}: {error}", path.display()))?;
        if count == 0 {
            break;
        }
        byte_length = byte_length
            .checked_add(count as u64)
            .ok_or("prepared snapshot byte length overflow")?;
        for byte in &buffer[..count] {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    Ok((format!("{hash:016x}"), byte_length))
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

/// Whether `instance_mir(Item(def_id))` has source MIR even when the
/// cross-crate optimized-MIR availability query is false. Rustc stores ADT
/// constructor bodies and always-const function bodies in the CTFE MIR table;
/// `instance_mir` routes those exact kinds to `mir_for_ctfe` instead of
/// `optimized_mir`.
fn has_instance_mir_source<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::DefId) -> bool {
    if tcx.is_mir_available(def_id) {
        return true;
    }
    match tcx.def_kind(def_id) {
        rustc_hir::def::DefKind::Ctor(..) => true,
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => matches!(
            tcx.constness(def_id),
            rustc_hir::Constness::Const { always: true }
        ),
        _ => false,
    }
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
        let mut matches = local_definitions
            .iter()
            .copied()
            .filter(|def_id| tcx.def_path_str(def_id.to_def_id()) == *requested)
            .collect::<Vec<_>>();
        let had_path_match = !matches.is_empty();
        // Pinned rustc_mir_transform::is_mir_available uses mir_keys: body
        // owners (plus generated bodies/constructors), not every HIR item.
        // Path-transparent foreign blocks inside a function can print the
        // same def-path as that function, but cannot be exported as MIR roots.
        matches.retain(|def_id| tcx.is_mir_available(def_id.to_def_id()) &&
            !is_required_trait_method(tcx, def_id.to_def_id()));
        let [def_id] = matches.as_slice() else {
            return Err(if matches.is_empty() {
                if had_path_match {
                    format!("--root {requested:?} has no available MIR body")
                } else {
                    format!("--root {requested:?} did not resolve to a local MIR body")
                }
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

fn mir_phase_json(phase: rustc_middle::mir::MirPhase) -> pool_body::Phase {
    use rustc_middle::mir::{AnalysisPhase as A, MirPhase as M, RuntimePhase as R};
    match phase {
        M::Built => pool_body::Phase::Built,
        M::Analysis(phase) => pool_body::Phase::Analysis { phase: match phase {
            A::Initial => pool_body::AnalysisPhase::Initial,
            A::PostCleanup => pool_body::AnalysisPhase::PostCleanup,
        } },
        M::Runtime(phase) => pool_body::Phase::Runtime { phase: match phase {
            R::Initial => pool_body::RuntimePhase::Initial,
            R::PostCleanup => pool_body::RuntimePhase::PostCleanup,
            R::Optimized => pool_body::RuntimePhase::Optimized,
        } },
    }
}

fn coroutine_kind_json(kind: rustc_hir::CoroutineKind) -> pool_body::CoroutineKind {
    use rustc_hir::{CoroutineDesugaring as D, CoroutineKind as K, CoroutineSource as S};
    match kind {
        K::Desugared(desugaring, source) => pool_body::CoroutineKind::Desugared { desugaring: match desugaring { D::Async => "async", D::Gen => "gen", D::AsyncGen => "async_gen" }, source: match source { S::Block => "block", S::Closure => "closure", S::Fn => "function" } },
        K::Coroutine(movability) => pool_body::CoroutineKind::Coroutine { movability: match movability { rustc_hir::Movability::Static => "static", rustc_hir::Movability::Movable => "movable" } },
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

fn fake_read_cause_json(context: &mut ExportContext<'_>, cause: rustc_middle::mir::FakeReadCause) -> pool_body::FakeReadCause {
    use rustc_middle::mir::FakeReadCause as F;
    use pool_body::FakeReadCause as C;
    match cause {
        F::ForMatchGuard => C::MatchGuard,
        F::ForMatchedPlace(def_id) => C::MatchedPlace { hoisted_from: def_id.map(|id| def_json(context, id.to_def_id())) },
        F::ForGuardBinding => C::GuardBinding,
        F::ForLet(def_id) => C::LetBinding { hoisted_from: def_id.map(|id| def_json(context, id.to_def_id())) },
        F::ForIndex => C::Index,
    }
}

fn runtime_check_json(tcx: TyCtxt<'_>, check: rustc_middle::mir::RuntimeChecks) -> pool_body::RuntimeCheck {
    use rustc_middle::mir::RuntimeChecks as R;
    use pool_body::RuntimeCheck as C;
    let enabled = check.value(tcx.sess);
    match check {
        R::UbChecks => C::UbChecks { enabled },
        R::ContractChecks => C::ContractChecks { enabled },
        R::OverflowChecks => C::OverflowChecks { enabled },
    }
}

fn bound_region_kind_json(context: &mut ExportContext<'_>, tcx: TyCtxt<'_>, kind: ty::BoundRegionKind<'_>) -> pool_values::BoundRegionKind {
    use pool_values::BoundRegionKind as O;
    match kind { ty::BoundRegionKind::Anon => O::Anonymous, ty::BoundRegionKind::NamedForPrinting(name) => O::NamedForPrinting { name: name.to_string() }, ty::BoundRegionKind::Named(def) => O::Named { def_id: def_json(context,def), def_path: tcx.def_path_str(def) }, ty::BoundRegionKind::ClosureEnv => O::ClosureEnvironment }
}
fn region_json(context: &mut ExportContext<'_>, tcx: TyCtxt<'_>, region: ty::Region<'_>) -> Result<pool_values::Region, String> {
    use ty::RegionKind as R;
    use pool_values::{Region as O, BoundIndex as I, LateParameter as L};
    Ok(match region.kind() {
        R::ReEarlyParam(p) => O::EarlyParameter { index:p.index, name:p.name.to_string() },
        R::ReBound(index,b) => O::Bound { index_kind:match index { ty::BoundVarIndexKind::Bound(i)=>I::Bound { debruijn_index:i.as_u32() }, ty::BoundVarIndexKind::Canonical=>I::Canonical }, variable_index:b.var.as_u32(), bound_kind:bound_region_kind_json(context,tcx,b.kind) },
        R::ReLateParam(p) => O::LateParameter { scope_def_id:def_json(context,p.scope), scope_def_path:tcx.def_path_str(p.scope), parameter:match p.kind { ty::LateParamRegionKind::Anon(index)=>L::Anonymous {index}, ty::LateParamRegionKind::NamedAnon(index,name)=>L::NamedAnonymous {index,name:name.to_string()}, ty::LateParamRegionKind::Named(def)=>L::Named {def_id:def_json(context,def),def_path:tcx.def_path_str(def)}, ty::LateParamRegionKind::ClosureEnv=>L::ClosureEnvironment } },
        R::ReStatic=>O::Static,
        R::ReVar(v)=>return export_failure("region",format!("unresolved inference variable {}",v.as_u32())),
        R::RePlaceholder(p)=>O::Placeholder {universe:p.universe().as_u32(),variable_index:p.bound.var.as_u32(),bound_kind:bound_region_kind_json(context,tcx,p.bound.kind)},
        R::ReErased=>O::Erased,
        R::ReError(_)=>return export_failure("main::region_json","error"),
    })
}

// Numeric fields come from the parsed compiler TargetDataLayout. Its private
// address-space inventory and _is_fat bit have no public accessors. Enumerate
// those only from the official LLVM data-layout input, following the pinned
// rustc_abi parser's p/pf directive and instruction-space inheritance rules.
fn runtime_target_data_layout_json(tcx: TyCtxt<'_>) -> Result<producer::TargetDataLayout, String> {
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
        producer::PointerSpec {
            pointer_size_bytes: dl.pointer_size_in(space).bytes(),
            pointer_align_bytes: dl.pointer_align_in(space).bytes(),
            pointer_offset_bytes: dl.pointer_offset_in(space).bytes(), is_fat: fat,
        }
    };
    let bound = |space: AddressSpace| match dl.pointer_size_in(space).bits() {
        16 | 32 | 64 => Some(dl.obj_size_bound_in(space)),
        _ => None,
    };
    let complete = bound(dl.default_address_space).is_some()
        && spaces.iter().all(|(space, _)| bound(*space).is_some());
    if !complete {
        export_failure::<()>(
            "target data layout",
            "object-size query supports only 16/32/64-bit pointers",
        )?;
    }
    let address_space_info = spaces
        .iter()
        .map(|(space, fat)| {
            producer::AddressSpaceInfo { address_space: space.0, spec: spec(*space, *fat),
                object_size_bound_bytes: bound(*space) }
        })
        .collect::<Vec<_>>();
    Ok(producer::TargetDataLayout {
        evidence_path: "rustc_abi/src/lib.rs::TargetDataLayout; TyCtxt::data_layout",
        llvm_data_layout: llvm,
        private_inventory_evidence: "p/pf directives and instruction-space inheritance from pinned TargetDataLayout::parse_from_llvm_datalayout_string",
        alignment_evidence: "pinned TargetDataLayout stores ABI Align only; preferred LLVM alignment entries remain in llvm_data_layout",
        endian: match dl.endian { Endian::Little => "little", Endian::Big => "big" },
        pointer_width_bits: dl.pointer_size().bits(),
        object_size_bound_bytes: bound(dl.default_address_space),
        i1_align_bytes: dl.i1_align.bytes(),i8_align_bytes: dl.i8_align.bytes(),
        i16_align_bytes: dl.i16_align.bytes(),i32_align_bytes: dl.i32_align.bytes(),
        i64_align_bytes: dl.i64_align.bytes(),i128_align_bytes: dl.i128_align.bytes(),
        f16_align_bytes: dl.f16_align.bytes(),f32_align_bytes: dl.f32_align.bytes(),
        f64_align_bytes: dl.f64_align.bytes(),f128_align_bytes: dl.f128_align.bytes(),
        aggregate_align_bytes: dl.aggregate_align.bytes(),
        vector_align: dl.vector_align.iter().map(|(size,align)|producer::VectorAlign {size_bytes: size.bytes(),align_bytes: align.bytes()}).collect::<Vec<_>>(),
        default_address_space: dl.default_address_space.0,
        default_address_space_pointer_spec: spec(dl.default_address_space,default_fat),
        address_space_info: address_space_info,
        instruction_address_space: dl.instruction_address_space.0,
        c_enum_min_size: match dl.c_enum_min_size {
            rustc_abi::Integer::I8 => "I8", rustc_abi::Integer::I16 => "I16",
            rustc_abi::Integer::I32 => "I32", rustc_abi::Integer::I64 => "I64",
            rustc_abi::Integer::I128 => "I128",
        },
    })
}

/// Shim signatures are queried by reached foreign dispatch, not by the mere
/// existence of a Rust main. Startup queries are exported by their own producers.
/// Generated MIR can introduce another foreign demand in a later round.
#[derive(Default, serde::Serialize)]
struct RuntimeCatalogs {
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_named_types: Option<NamedTypes>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_shim_abis: Option<Vec<shim_abi::Recipe>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_named_shim_abis: Option<Vec<shim_abi::NamedSignature>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_libc_type_layouts: Option<libc_type_layouts::Catalog>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_windows_type_layouts: Option<windows_type_layouts::Catalog>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_named_constants: Option<Vec<NamedConstant>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    compiler_named_statics: Option<Vec<named_statics::Record>>,
}
#[derive(serde::Serialize)]
#[serde(untagged)]
enum NamedTypes {
    Startup(shim_abi::StartupNamedTypes),
    All(BTreeMap<String, u64>),
}
#[derive(serde::Serialize)]
#[serde(untagged)]
enum NamedConstant {
    Libc(named_constants::Record),
    Windows(windows_constants::Record),
}
#[derive(Default)]
struct RuntimeCatalogFacts {
    compiler_named_types: Option<NamedTypes>,
    compiler_shim_abis: Option<Vec<shim_abi::Recipe>>,
    compiler_named_shim_abis: Option<Vec<shim_abi::NamedSignature>>,
    compiler_libc_type_layouts: Option<libc_type_layouts::Catalog>,
    compiler_windows_type_layouts: Option<windows_type_layouts::Catalog>,
    compiler_named_constants: Option<Vec<NamedConstant>>,
    compiler_named_statics: Option<Vec<named_statics::Record>>,
}
impl RuntimeCatalogFacts {
    fn finish(self) -> RuntimeCatalogs {
        RuntimeCatalogs {
            compiler_named_types: self.compiler_named_types,
            compiler_shim_abis: self.compiler_shim_abis,
            compiler_named_shim_abis: self.compiler_named_shim_abis,
            compiler_libc_type_layouts: self.compiler_libc_type_layouts,
            compiler_windows_type_layouts: self.compiler_windows_type_layouts,
            compiler_named_constants: self.compiler_named_constants,
            compiler_named_statics: self.compiler_named_statics,
        }
    }
}
fn runtime_catalogs_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<RuntimeCatalogFacts, String> {
    let named_shim_abis = shim_abi::named_signatures(tcx, context)?;
    let mut os_shims = !named_shim_abis.is_empty();
    let names = context
        .pending_instances
        .iter()
        .filter(|instance| tcx.is_foreign_item(instance.def_id()))
        .map(|instance| tcx.symbol_name(*instance).name)
        .collect::<Vec<_>>();
    // These source match arms precede target-specific dispatch. Unknown
    // foreign declarations need their identity/ABI, not unrelated OS queries.
    let c_shim = names.iter().any(|name| {
        matches!(
            *name,
            "exit"
                | "abort"
                | "malloc"
                | "calloc"
                | "realloc"
                | "free"
                | "malloc_usable_size"
                | "memcmp"
                | "memcpy"
                | "memset"
                | "memchr"
                | "memrchr"
                | "strlen"
                | "strnlen"
                | "strcpy"
                | "wcslen"
        )
    });
    // helpers.rs::read_wchar_t_str uses u16 on Windows and libc::wchar_t elsewhere.
    os_shims |= names.contains(&"wcslen") && tcx.sess.target.os != rustc_target::spec::Os::Windows;
    let miri_shim = names.iter().any(|name| name.starts_with("miri_"));
    let no_alloc = rustc_symbol_mangling::mangle_internal_symbol(
        tcx,
        rustc_ast::expand::allocator::NO_ALLOC_SHIM_IS_UNSTABLE,
    );
    let no_alloc_shim = names.contains(&no_alloc.as_str());
    let allocator = tcx.allocator_kind(()).is_some_and(|kind| {
        rustc_codegen_ssa::base::allocator_shim_contents(tcx, kind)
            .iter()
            .any(|method| {
                method.special.is_some()
                    && names.contains(
                        &rustc_symbol_mangling::mangle_internal_symbol(
                            tcx,
                            &rustc_ast::expand::allocator::global_fn_name(method.name),
                        )
                        .as_str(),
                    )
            })
    });
    let portable = c_shim || miri_shim || no_alloc_shim || allocator;
    let mut fields = RuntimeCatalogFacts::default();
    if tcx
        .crate_types()
        .contains(&rustc_structures::CrateType::Executable)
        && !rustc_attr_ir::find_attr!(tcx, crate, NoCore)
    {
        fields.compiler_named_types = Some(NamedTypes::Startup(shim_abi::startup_named_types(
            tcx, context,
        )?));
    }
    if !os_shims && !portable {
        return Ok(fields);
    }
    fields.compiler_shim_abis = Some(shim_abi::export(
        tcx,
        context,
        !os_shims && !miri_shim && !no_alloc_shim && !allocator,
        tcx.entry_fn(()).is_some() || allocator,
    )?);
    if os_shims {
        fields.compiler_named_shim_abis = Some(named_shim_abis);
        fields.compiler_named_types = Some(NamedTypes::All(shim_abi::named_types(tcx, context)?));
        fields.compiler_libc_type_layouts = Some(libc_type_layouts::export(tcx, context)?);
        fields.compiler_windows_type_layouts = Some(windows_type_layouts::export(tcx, context)?);
        let mut constants = named_constants::export(tcx, context)?
            .into_iter()
            .map(NamedConstant::Libc)
            .collect::<Vec<_>>();
        constants.extend(
            windows_constants::export(tcx, context)?
                .into_iter()
                .map(NamedConstant::Windows),
        );
        fields.compiler_named_constants = Some(constants);
        fields.compiler_named_statics = Some(named_statics::export(tcx, context)?);
    }
    Ok(fields)
}

#[derive(serde::Serialize)]
struct RuntimePrimitives {
    u8: u64,
    u16: u64,
    u32: u64,
    u64: u64,
    u128: u64,
    i8: u64,
    i16: u64,
    i32: u64,
    i64: u64,
    i128: u64,
    bool: u64,
    pointer_tag_integer: u64,
    usize: u64,
    isize: u64,
    unit: u64,
    unit_pointer_const: u64,
    unit_pointer_mut: u64,
    imm_u8_pointer: u64,
    imm_u8_pointer_pointer: u64,
    type_name_result_type: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    caller_location_type: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ordering_enum: Option<u64>,
}

impl ExportCallbacks {
    fn export_document<'tcx>(&mut self, tcx: TyCtxt<'tcx>) -> Result<Compilation, String> {
        #[cfg(feature = "miri-reference")]
        let reference_entry = if self.miri_reference {
            if !self.prepared_allocator_world {
                return Err(
                    "same-TyCtxt Miri reference requires the prepared allocator-world profile"
                        .into(),
                );
            }
            if tcx
                .crate_types()
                .contains(&rustc_structures::CrateType::Executable)
            {
                // Resolve the entry point before allocator_world::capture freezes
                // its final source AllocId sentinel. No exporter query may occur
                // between that capture and Miri's actual evaluation.
                Some(miri::entry_fn(tcx))
            } else {
                None
            }
        } else {
            None
        };
        let items = tcx.hir_crate_items(());
        let mut local_definitions = items
            .definitions()
            .chain(items.nested_bodies())
            .collect::<HashSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        local_definitions.sort_by_key(|def_id| tcx.def_path_str(def_id.to_def_id()));
        let selected_roots = select_roots(tcx, &local_definitions, &self.root_paths)?;
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
                        && !ty::GenericArgs::identity_for_item(tcx, def.to_def_id())
                            .has_non_region_param()
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
                        && !ty::GenericArgs::identity_for_item(tcx, def_id.to_def_id())
                            .has_non_region_param()
                }
            })
            .map(|def_id| export_body(tcx, def_id, &mut export_context))
            .collect::<Result<Vec<_>, String>>()?;
        // eval.rs main compiler queries must enqueue actual lang_start MIR
        // before the shared reachable-instance traversal.
        let main_queries = main_queries::export(tcx, &mut export_context, &main_query_roots)?;
        // Canonical primitive identities for runtime array constructors.
        let mut runtime_primitives = RuntimePrimitives {
            u8: type_json(&mut export_context, tcx, tcx.types.u8)?,
            u16: type_json(&mut export_context, tcx, tcx.types.u16)?,
            u32: type_json(&mut export_context, tcx, tcx.types.u32)?,
            u64: type_json(&mut export_context, tcx, tcx.types.u64)?,
            u128: type_json(&mut export_context, tcx, tcx.types.u128)?,
            i8: type_json(&mut export_context, tcx, tcx.types.i8)?,
            i16: type_json(&mut export_context, tcx, tcx.types.i16)?,
            i32: type_json(&mut export_context, tcx, tcx.types.i32)?,
            i64: type_json(&mut export_context, tcx, tcx.types.i64)?,
            i128: type_json(&mut export_context, tcx, tcx.types.i128)?,
            bool: type_json(&mut export_context, tcx, tcx.types.bool)?,
            pointer_tag_integer: type_json(&mut export_context, tcx, {
                use rustc_middle::ty::layout::IntegerExt;
                tcx.data_layout.ptr_sized_integer().to_ty(tcx, false)
            })?,
            usize: type_json(&mut export_context, tcx, tcx.types.usize)?,
            isize: type_json(&mut export_context, tcx, tcx.types.isize)?,
            unit: type_json(&mut export_context, tcx, tcx.types.unit)?,
            unit_pointer_const: type_json(
                &mut export_context,
                tcx,
                ty::Ty::new_imm_ptr(tcx, tcx.types.unit),
            )?,
            unit_pointer_mut: type_json(
                &mut export_context,
                tcx,
                ty::Ty::new_mut_ptr(tcx, tcx.types.unit),
            )?,
            imm_u8_pointer: type_json(
                &mut export_context,
                tcx,
                ty::Ty::new_imm_ptr(tcx, tcx.types.u8),
            )?,
            imm_u8_pointer_pointer: type_json(
                &mut export_context,
                tcx,
                ty::Ty::new_imm_ptr(tcx, ty::Ty::new_imm_ptr(tcx, tcx.types.u8)),
            )?,
            // Seed the intrinsic's actual result before the finite runtime
            // query domain is captured; late ConstValue export must not leave
            // its &str layout without the corresponding compiler leaves.
            type_name_result_type: type_json(
                &mut export_context,
                tcx,
                ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.str_),
            )?,
            caller_location_type: None,
            ordering_enum: None,
        };
        if tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::PanicLocation)
            .is_some()
        {
            runtime_primitives.caller_location_type = Some(type_json(
                &mut export_context,
                tcx,
                tcx.caller_location_ty(),
            )?);
        }
        if tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::OrderingEnum)
            .is_some()
        {
            runtime_primitives.ordering_enum = Some(type_json(
                &mut export_context,
                tcx,
                tcx.ty_ordering_enum(rustc_span::DUMMY_SP),
            )?);
        }
        if tcx.entry_fn(()).is_some() {
            panic_queries::register_termination_helpers(tcx, &mut export_context)?;
        }
        let mut native_state = native_signature_queries::State::default();
        let mut type_name_state = intrinsic_value_queries::TypeNames::default();
        let mut retag_state = retag_queries::State::default();
        let mut global_byte_state = global_byte_queries::State::default();
        let mut identity_state = IdentityDiscovery::default();
        let mut function_state = FunctionDiscovery::default();
        let mut predicate_facts = Vec::new();
        let mut instances = export_reachable_instances(tcx, &mut export_context)?;
        // Seed erased signature types before the finite runtime-query domain.
        let _ = native_signature_queries::discover(tcx, &mut export_context, &mut native_state)?;
        let _ = cast_queries::discover(tcx, &mut export_context)?;
        instances.extend(export_reachable_instances(tcx, &mut export_context)?);
        let _intrinsic_type_names_seed =
            intrinsic_value_queries::discover_type_names(tcx, &mut export_context, &mut type_name_state)?;
        let _caller_location_constants_seed =
            intrinsic_value_queries::discover_caller_locations(tcx, &mut export_context)?;
        let _ = compiler_vtable_queries_json(tcx, &mut export_context)?;
        let _predicate_queries_seed = compiler_predicate_queries_json(tcx, &mut export_context, &mut predicate_facts)?;
        let _native_signature_queries_seed =
            native_signature_queries::discover(tcx, &mut export_context, &mut native_state)?;
        let panic_facts = panic_queries::discover(tcx, &mut export_context);
        let _retag_queries_seed = retag_queries::discover(&mut export_context, &mut retag_state);
        let mut internal_target_features = tcx
            .sess
            .internal_target_features
            .iter()
            .map(|name| name.as_str().to_owned())
            .collect::<Vec<_>>();
        internal_target_features.sort();
        let root_span = span_json(&mut export_context, tcx, rustc_span::DUMMY_SP);
        // Close source-demand discovery before constructing query catalogs.
        // Request consumers retain cursors and completed compiler facts;
        // source-free pointer/ref outputs do not seed new runtime demands.
        let mut runtime_type_facts = Vec::new();
        let mut processed_runtime_type_queries = HashSet::new();
        let mut runtime_catalogs = None;
        let mut catalog_foreign_symbols = HashSet::new();
        let mut selected_alloc_id_keys = allocator_world::SelectedKeyProbes::new();
        let foreign_facts = loop {
            // Most accumulated domains are insertion-only, so cardinalities
            // prove that their keys did not change. These identity sets can
            // also lose members on upgrade; their exact net membership delta
            // is tracked without cloning both complete sets.
            export_context.identity_membership_delta.clear();
            let before = [
                export_context.instance_ids.len(),
                export_context.pending_instances.len(),
                export_context.emitted_instances.len(),
                export_context.type_ids.len(),
                export_context.type_ids.defined_len(),
                export_context.allocation_ids.len(),
                export_context.allocation_ids.defined_len(),
                export_context.predicate_ids.len(),
                export_context.pending_predicates.len(),
                export_context.cast_unsize_requests.len(),
                export_context.cast_box_requests.len(),
                export_context.vtable_query_requests.len(),
                export_context.dynamic_vtable_upcast_requests.len(),
                export_context.covariance_query_requests.len(),
                export_context.instance_abi_requests.len(),
                export_context.fn_pointer_abi_requests.len(),
                export_context.fn_pointer_targets.len(),
                export_context.runtime_mir_frame_instances.len(),
                export_context.fn_pointer_cast_inputs.len(),
                export_context.fn_pointer_call_transfers.len(),
                export_context.foreign_call_transfers.len(),
                export_context.processed_foreign_transfers.len(),
                export_context.runtime_callback_transfers.len(),
                export_context.runtime_callback_transfer_keys.len(),
                export_context.processed_runtime_callback_transfers.len(),
                export_context.runtime_catch_unwind_sites.len(),
                export_context.runtime_unwind_payload_types.len(),
                export_context.virtual_call_transfers.len(),
                export_context.processed_fn_pointer_transfers.len(),
                export_context.processed_virtual_transfers.len(),
                export_context.caller_location_spans.len(),
                export_context.caller_location_constant_rows.len(),
                export_context.symbol_only_instances.len(),
                export_context.runtime_query_only_empty_drops.len(),
                export_context.runtime_type_query_demands.len(),
                processed_runtime_type_queries.len(),
            ];
            let foreign_symbols = export_context
                .pending_instances
                .iter()
                .filter(|instance| tcx.is_foreign_item(instance.def_id()))
                .map(|instance| tcx.symbol_name(*instance).name.to_owned())
                .collect::<HashSet<_>>();
            if runtime_catalogs.is_none() || foreign_symbols != catalog_foreign_symbols {
                runtime_catalogs = Some(runtime_catalogs_json(tcx, &mut export_context)?);
                catalog_foreign_symbols = foreign_symbols;
            }
            cast_queries::discover(tcx, &mut export_context)?;
            compiler_vtable_queries_json(tcx, &mut export_context)?;
            let foreign_facts = foreign_symbols::discover(tcx, &mut export_context)?;
            compiler_runtime_virtual_queries_json(tcx, &mut export_context)?;
            register_fn_pointer_call_transfers(&mut export_context, tcx)?;
            register_runtime_callback_transfers(&mut export_context, tcx)?;
            let runtime_type_query_wave = compiler_runtime_type_queries_json(
                tcx,
                &mut export_context,
                &mut processed_runtime_type_queries,
            )?;
            runtime_type_facts.extend(runtime_type_query_wave);
            global_byte_queries::discover(tcx, &mut export_context, &mut global_byte_state)?;
            identity_only_instances_json(tcx, &mut export_context, &mut identity_state)?;
            compiler_instance_abis_json(tcx, &mut export_context)?;
            covariance_queries::discover(tcx, &mut export_context)?;
            compiler_function_facts_json(tcx, &mut export_context, &mut function_state)?;
            compiler_predicate_queries_json(tcx, &mut export_context, &mut predicate_facts)?;
            native_signature_queries::discover(tcx, &mut export_context, &mut native_state)?;
            retag_queries::discover(&mut export_context, &mut retag_state);
            intrinsic_value_queries::discover_type_names(tcx, &mut export_context, &mut type_name_state)?;
            intrinsic_value_queries::discover_caller_locations(tcx, &mut export_context)?;
            instances.extend(export_reachable_instances(tcx, &mut export_context)?);
            if self.prepared_allocator_world {
                register_backtrace_frame_pointer_demands(tcx, &mut export_context);
                selected_alloc_id_keys.probe_round(tcx, &mut export_context)?;
            }
            let after = [
                export_context.instance_ids.len(),
                export_context.pending_instances.len(),
                export_context.emitted_instances.len(),
                export_context.type_ids.len(),
                export_context.type_ids.defined_len(),
                export_context.allocation_ids.len(),
                export_context.allocation_ids.defined_len(),
                export_context.predicate_ids.len(),
                export_context.pending_predicates.len(),
                export_context.cast_unsize_requests.len(),
                export_context.cast_box_requests.len(),
                export_context.vtable_query_requests.len(),
                export_context.dynamic_vtable_upcast_requests.len(),
                export_context.covariance_query_requests.len(),
                export_context.instance_abi_requests.len(),
                export_context.fn_pointer_abi_requests.len(),
                export_context.fn_pointer_targets.len(),
                export_context.runtime_mir_frame_instances.len(),
                export_context.fn_pointer_cast_inputs.len(),
                export_context.fn_pointer_call_transfers.len(),
                export_context.foreign_call_transfers.len(),
                export_context.processed_foreign_transfers.len(),
                export_context.runtime_callback_transfers.len(),
                export_context.runtime_callback_transfer_keys.len(),
                export_context.processed_runtime_callback_transfers.len(),
                export_context.runtime_catch_unwind_sites.len(),
                export_context.runtime_unwind_payload_types.len(),
                export_context.virtual_call_transfers.len(),
                export_context.processed_fn_pointer_transfers.len(),
                export_context.processed_virtual_transfers.len(),
                export_context.caller_location_spans.len(),
                export_context.caller_location_constant_rows.len(),
                export_context.symbol_only_instances.len(),
                export_context.runtime_query_only_empty_drops.len(),
                export_context.runtime_type_query_demands.len(),
                processed_runtime_type_queries.len(),
            ];
            if before == after && export_context.identity_membership_delta.is_empty() {
                break foreign_facts;
            }
        };
        let startup_facts = if tcx.crate_types().contains(&rustc_structures::CrateType::Executable) {
            Some(startup_queries::discover(tcx, &mut export_context)?)
        } else { None };
        // All discovery has converged. These projections consume retained
        // facts and borrow the completed graph without registering new keys.
        let cast_queries = cast_queries::finish(std::mem::take(&mut export_context.cast_state.rows));
        let vtable_facts = std::mem::take(&mut export_context.vtable_state.rows);
        let (vtable_queries, vtable_query_ids) = finish_vtable_queries(vtable_facts, &export_context);
        let runtime_virtual_queries = std::mem::take(&mut export_context.virtual_state.rows)
            .into_iter().map(|fact| fact.finish(&vtable_query_ids)).collect::<Result<Vec<_>, _>>()?;
        let runtime_foreign_symbols = foreign_symbols::finish(tcx, foreign_facts);
        let runtime_caller_instances = compiler_caller_location_queries_json(tcx, &export_context)?;
        let global_byte_queries = global_byte_queries::finish(global_byte_state, &export_context);
        let instance_abis = std::mem::take(&mut export_context.abi_state.rows)
            .into_iter().map(InstanceAbiFact::finish).collect();
        let covariance_requests = export_context.covariance_pairs.iter().copied().collect();
        let covariance_queries = covariance_queries::evaluate(tcx, &export_context, covariance_requests)?;
        let function_facts = function_state.finish();
        let predicate_queries = finish_predicate_queries(tcx, &export_context, predicate_facts);
        let native_signature_queries = native_signature_queries::finish(native_state, &export_context);
        let retag_queries = retag_queries::finish(tcx, &export_context);
        let intrinsic_type_names = intrinsic_value_queries::finish_type_names(type_name_state);
        let caller_location_constants = intrinsic_value_queries::finish_caller_locations(tcx, &export_context);
        let runtime_type_queries = runtime_type_facts.into_iter().map(RuntimeTypeFact::finish).collect();
        let mut instances = instances.into_iter().map(InstanceFact::finish).collect::<Vec<_>>();
        instances.extend(identity_state.finish(&export_context));
        instances.sort_by_key(|row| row.instance_id);
        if instances.len() != export_context.instance_ids.len()
            || instances
                .iter()
                .enumerate()
                .any(|(id, row)| row.instance_id != id as u64)
        {
            return Err("instance table has missing or duplicate definitions".into());
        }
        let runtime_queries = RuntimeQueries {
            startup: startup_facts.map(startup_queries::finish),
            types: runtime_type_queries,
            virtual_queries: runtime_virtual_queries,
            instances: runtime_caller_instances,
            foreign_symbols: runtime_foreign_symbols,
        };
        // Preserve compiler query evaluation order before capturing allocator state.
        let producer = Producer {
            miri_commit: MIRI_COMMIT,
            rustc_commit: EXPECTED_RUSTC_COMMIT,
            rustc_version: self.rustc_version.clone(),
            target_triple: tcx.sess.opts.target_triple.to_string(),
            input_settings: producer::evidence(
                tcx,
                self.invocation
                    .as_ref()
                    .ok_or("missing invocation evidence")?
                    .rustc_args(),
            )?,
        };
        let target_data_layout = runtime_target_data_layout_json(tcx)?;
        let frame_metadata = compiler_frame_metadata_json(tcx);
        let panic_query_catalog = panic_queries::finish(panic_facts);
        let runtime_checks = [
            runtime_check_json(tcx, rustc_middle::mir::RuntimeChecks::UbChecks),
            runtime_check_json(tcx, rustc_middle::mir::RuntimeChecks::ContractChecks),
            runtime_check_json(tcx, rustc_middle::mir::RuntimeChecks::OverflowChecks),
        ];
        let session_queries = SessionQueries {
            internal_target_features,
            is_like_wasm: tcx.sess.target.is_like_wasm,
            target_arch: tcx.sess.target.arch.to_string(),
            root_span,
            runtime_checks,
        };
        let selected_scope = if is_scoped {
            Some(SelectedScope {
                kind: "rooted_structural_closure",
                semantics: "structural_export_closure_only",
                roots: selected_roots
                    .iter()
                    .map(|def_id| SelectedRoot {
                        def_path: tcx.def_path_str(def_id.to_def_id()),
                        def_id: def_json(&mut export_context, def_id.to_def_id()),
                    })
                    .collect(),
                dependency_policy: "canonical entry instances and transitive MIR/type-shape/layout/allocation references",
            })
        } else {
            None
        };
        for (id, instance) in instances.into_iter().enumerate() {
            export_context.instance_ids.define(id, instance);
        }
        let body_roots = bodies;
        let allocator_world = if self.prepared_allocator_world {
            Some(allocator_world::capture(
                tcx,
                &mut export_context,
                selected_alloc_id_keys,
            )?)
        } else {
            None
        };
        let vtable_diagnostics = export_context
            .vtable_diagnostics
            .report(&export_context, &vtable_query_ids)?;
        if tcx.dcx().has_errors().is_some() {
            return Err("compiler reported errors while exporting semantic metadata".into());
        }
        if export_context.type_ids.defined_len() != export_context.type_ids.len()
            || !export_context.type_nodes_in_progress.is_empty()
            || export_context.allocation_ids.defined_len() != export_context.allocation_ids.len()
            || !export_context.allocations_in_progress.is_empty()
            || export_context.predicate_ids.defined_len() != export_context.predicate_ids.len()
            || !export_context.predicates_in_progress.is_empty()
        {
            return Err("type or allocation table has unfinished definitions".into());
        }
        let candidates = query_values::virtual_candidates(&runtime_queries.virtual_queries);
        let bodies = export_context
            .bodies
            .finish("body")?
            .into_iter()
            .map(|body| body.finish(&vtable_query_ids, &candidates))
            .collect::<Result<Vec<_>, _>>()?;
        let document = ExportDocument {
            schema: "lean-miri-rustc-mir",
            schema_version: ROOT_SCHEMA_VERSION,
            mir_query: "TyCtxt::instance_mir(InstanceKind::Item(def_id)); ordinary runtime function bodies use optimized_mir",
            compiler_abi_layout_schema: "physical_ty_and_layout_v1",
            producer,
            runtime_target_data_layout: target_data_layout,
            compiler_session_queries: session_queries,
            compiler_runtime_queries: runtime_queries,
            compiler_frame_metadata: frame_metadata,
            compiler_instance_abis: instance_abis,
            compiler_function_facts: function_facts,
            compiler_cast_queries: cast_queries,
            compiler_type_name_constants: intrinsic_type_names,
            compiler_panic_queries: panic_query_catalog,
            compiler_native_signature_queries: native_signature_queries,
            compiler_retag_queries: retag_queries,
            compiler_covariance_queries: covariance_queries,
            compiler_global_byte_queries: global_byte_queries,
            compiler_caller_location_constants: caller_location_constants,
            compiler_main_queries: main_queries,
            compiler_runtime_primitives: runtime_primitives,
            compiler_vtable_queries: vtable_queries,
            compiler_predicate_queries: predicate_queries,
            runtime_catalogs: runtime_catalogs.unwrap_or_default().finish(),
            body_roots,
            bodies,
            definitions: export_context.definitions.finish("definition")?,
            type_constants: export_context.type_constants.finish("type_constant")?,
            files: export_context.files.finish(),
            spans: export_context.spans.finish("span_id")?,
            layouts: export_context.layouts.finish("layout_id")?,
            fn_abis: export_context.fn_abis.finish("fn_abi_id")?,
            instances: export_context.instance_ids.finish("instance_id")?,
            types: export_context.type_ids.finish("type_id")?,
            byte_images: export_context.byte_images.finish(),
            allocations: allocation_values::compact(export_context.allocation_ids.finish("allocation_id")?),
            predicates: export_context.predicate_ids.finish("predicate_id")?,
            compiler_alloc_id_world: allocator_world,
            selected_scope,
            invocation: self.invocation.take(),
        };
        #[cfg(feature = "miri-reference")]
        let miri_reference_frontier = document
            .compiler_alloc_id_world
            .as_ref()
            .map(|world| world.frontier.last_reserved_source_alloc_id);
        self.diagnostics = vtable_diagnostics;
        if self.miri_reference {
            if !self.prepared_allocator_world {
                return Err(
                    "same-TyCtxt Miri reference requires the prepared allocator-world profile"
                        .into(),
                );
            }
            write_document(&self.output, &document)?;
            vtable_diagnostics::write_report(self.diagnostics.take(), &self.output)?;
            #[cfg(feature = "miri-reference")]
            {
                let (fingerprint, byte_length) = snapshot_fingerprint(&self.output)?;
                let Some(frontier) = miri_reference_frontier else {
                    return Err("prepared allocator-world snapshot omitted its final source AllocId frontier"
                            .into());
                };
                let sidecar = reference_sidecar_path(&self.output);
                let mut sidecar_record = reference_values::Sidecar {
                    snapshot_fnv1a64: fingerprint,
                    snapshot_byte_length: byte_length,
                    snapshot_path: self.output.to_string_lossy().into_owned(),
                    last_reserved_source_alloc_id: frontier,
                    rustc_commit: EXPECTED_RUSTC_COMMIT,
                    miri_commit: MIRI_COMMIT,
                    reference_contract: "same_prepared_tcx_after_snapshot_capture;not_vanilla_miri_alloc_id_history",
                    status: reference_values::Status::Running,
                    reference: None,
                };
                write_document(&sidecar, &sidecar_record)?;
                // Drop the large owned snapshot tree before Miri starts using
                // the same TyCtxt, keeping the reference peak within budget.
                drop(document);
                let result = match reference_entry {
                    Some((entry, entry_type)) => run_prepared_miri_reference_entry(
                        tcx,
                        entry,
                        entry_type,
                        &self.miri_reference_args,
                    ),
                    None => reference_values::Result::skipped(),
                };
                sidecar_record.status = result.status();
                let failed = sidecar_record.status == reference_values::Status::Failed;
                sidecar_record.reference = Some(result);
                write_document(&sidecar, &sidecar_record)?;
                if failed {
                    return Err(
                        "same-TyCtxt Miri reference failed; see its reference sidecar".into(),
                    );
                }
                return Ok(if self.continue_compilation {
                    Compilation::Continue
                } else {
                    Compilation::Stop
                });
            }
        }
        if self.write_during_analysis {
            write_document(&self.output, &document)?;
            vtable_diagnostics::write_report(self.diagnostics.take(), &self.output)?;
            if self.continue_compilation {
                return Ok(Compilation::Continue);
            }
        }
        self.document = Some(document);
        Ok::<_, String>(if self.continue_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        })
    }
}

impl Callbacks for ExportCallbacks {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        match self.export_document(tcx) {
            Ok(outcome) => outcome,
            Err(error) => {
                self.export_error = Some(error);
                Compilation::Stop
            }
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
    let invocation = Invocation::Direct {
        rustc_commit:EXPECTED_RUSTC_COMMIT, rustc_executable:resolve_executable(selected_rustc),
        working_directory:env::current_dir().ok().map(|path|path.to_string_lossy().into_owned()),
        rustc_args:rustc_args[1..].to_vec(), rustc_args_fingerprint_fnv1a64:args_fingerprint(&rustc_args[1..]),
        root_paths:options.root_paths.clone(),
    };
    let miri_reference = prepared_miri_reference_enabled()?;
    let prepared_allocator_world = prepared_allocator_world_enabled()?;
    if miri_reference && !prepared_allocator_world {
        return Err(
            "same-TyCtxt Miri reference requires LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1".into(),
        );
    }
    #[cfg(feature = "miri-reference")]
    let miri_reference_args = if miri_reference {
        prepared_miri_reference_arguments()?
    } else {
        Vec::new()
    };
    let mut callbacks = ExportCallbacks {
        output: options.output,
        root_paths: options.root_paths,
        rustc_version,
        document: None,
        diagnostics: None,
        invocation: Some(invocation),
        write_during_analysis: false,
        continue_compilation: false,
        prepared_allocator_world,
        miri_reference,
        #[cfg(feature = "miri-reference")]
        miri_reference_args,
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
    if callbacks.miri_reference {
        return Ok(());
    }
    let document = callbacks
        .document
        .ok_or("rustc completed without after_analysis output")?;
    write_document(&callbacks.output, &document)?;
    vtable_diagnostics::write_report(callbacks.diagnostics.take(), &callbacks.output)
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

    let target_crate = flag_value(rustc_args, "--target").is_some();
    let mut rustc_args = rustc_args.to_vec();
    if !target_crate {
        // run_cargo always supplies --target for guest crates. Host build
        // scripts, proc macros and their dependencies execute on the host;
        // they are compilation tools, not inputs to the Lean interpreter.
        if !has_flag(&rustc_args, "--sysroot") {
            if let Some(sysroot) = env::var_os("MIRI_HOST_SYSROOT") {
                rustc_args.push("--sysroot".into());
                rustc_args.push(sysroot.to_string_lossy().into_owned());
            }
        }
        let status = Command::new(&rustc_path)
            .args(&rustc_args)
            .status()
            .map_err(|error| format!("cannot compile host tool with pinned rustc: {error}"))?;
        return if status.success() {
            Ok(())
        } else {
            Err(format!("host tool compilation exited with {status}"))
        };
    }
    let crate_name = flag_value(&rustc_args, "--crate-name")
        .ok_or("Cargo rustc invocation has no --crate-name")?;
    let out_dir =
        flag_value(&rustc_args, "--out-dir").ok_or("Cargo rustc invocation has no --out-dir")?;
    append_miri_target_flags(&mut rustc_args)?;
    if !has_flag(&rustc_args, "--sysroot") {
        if let Some(sysroot) = env::var_os("MIRI_SYSROOT") {
            rustc_args.push("--sysroot".into());
            rustc_args.push(sysroot.to_string_lossy().into_owned());
        }
    }
    let output = cargo_export_path(&out_dir, &crate_name, &rustc_args)?;
    let invocation = Invocation::Cargo {
        rustc_commit:EXPECTED_RUSTC_COMMIT,
        rustc_executable:rustc_path.canonicalize().ok().map(|path|path.to_string_lossy().into_owned()).unwrap_or_else(||rustc_path.to_string_lossy().into_owned()),
        working_directory:env::current_dir().ok().map(|path|path.to_string_lossy().into_owned()),
        crate_name:crate_name.clone(), source_path:rustc_args.iter().find(|arg|arg.ends_with(".rs")).cloned(),
        target_crate, rustc_args:rustc_args.clone(), rustc_args_fingerprint_fnv1a64:args_fingerprint(&rustc_args),
    };
    let mut driver_args = Vec::with_capacity(rustc_args.len() + 1);
    driver_args.push(rustc_path.to_string_lossy().into_owned());
    driver_args.extend(rustc_args);
    let miri_reference = prepared_miri_reference_enabled()?;
    let prepared_allocator_world = prepared_allocator_world_enabled()?;
    if miri_reference && !prepared_allocator_world {
        return Err(
            "same-TyCtxt Miri reference requires LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1".into(),
        );
    }
    #[cfg(feature = "miri-reference")]
    let miri_reference_args = if miri_reference {
        prepared_miri_reference_arguments()?
    } else {
        Vec::new()
    };
    let mut callbacks = ExportCallbacks {
        output,
        root_paths: Vec::new(),
        rustc_version,
        document: None,
        diagnostics: None,
        invocation: Some(invocation),
        write_during_analysis: true,
        continue_compilation: true,
        prepared_allocator_world,
        miri_reference,
        #[cfg(feature = "miri-reference")]
        miri_reference_args,
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

fn write_document(path: &Path, document: &impl serde::Serialize) -> Result<(), String> {
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
    let file = fs::File::create(&temporary)
        .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
    let mut writer = std::io::BufWriter::new(file);
    serde_json::to_writer(&mut writer, document).map_err(|error| {
        if error.io_error_kind().is_some() {
            format!("cannot write {}: {error}", temporary.display())
        } else {
            error.to_string()
        }
    })?;
    writer
        .flush()
        .map_err(|error| format!("cannot write {}: {error}", temporary.display()))?;
    // Close the file before rename for platforms that do not allow renaming
    // an open file. A successful flush above guarantees the complete JSON
    // has reached the temporary file before it can replace the destination.
    drop(writer);
    fs::rename(&temporary, path)
        .map_err(|error| format!("cannot install {}: {error}", path.display()))
}

struct InstanceFact {
    instance_id: u64,
    instance_kind: pool_instance::InstanceKind,
    def_id: u64,
    def_path: String,
    generic_args: Vec<pool_values::GenericArgument>,
    data: pool_instance::InstanceData,
}
impl InstanceFact {
    fn finish(self) -> pool_instance::Instance {
        pool_instance::Instance {
            instance_id: self.instance_id, instance_kind: self.instance_kind,
            def_id: self.def_id, def_path: self.def_path,
            generic_args: self.generic_args, data: self.data,
        }
    }
}
fn export_reachable_instances<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<Vec<InstanceFact>, String> {
    let mut records = Vec::new();
    while context.reachable_instance_cursor < context.pending_instances.len() {
        let instance = context.pending_instances[context.reachable_instance_cursor];
        context.reachable_instance_cursor += 1;
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
                Some(id)
            } else {
                None
            };
            records.push(InstanceFact { instance_id:instance_id, instance_kind:instance_kind_json(context,tcx,instance.def)?, def_id:def_json(context,def_id), def_path:tcx.def_path_str(def_id), generic_args:generic_args_json(context,tcx,instance.args)?, data:pool_instance::InstanceData::IntrinsicDispatch { fallback_instance:fallback, reason:"Miri executes intrinsic semantics outside a MIR body" } });
            continue;
        }
        if matches!(instance.def, ty::InstanceKind::Item(_)) && tcx.is_foreign_item(def_id) {
            // A foreign declaration has no MIR by definition. Preserve the
            // exact compiler link name so the runtime can route it through
            // its foreign-item shim and retain Unsupported for unhandled calls.
            records.push(InstanceFact { instance_id:instance_id, instance_kind:instance_kind_json(context,tcx,instance.def)?, def_id:def_json(context,def_id), def_path:tcx.def_path_str(def_id), generic_args:generic_args_json(context,tcx,instance.args)?, data:pool_instance::InstanceData::ForeignItemNoMir { foreign_item:true,symbol_name:tcx.symbol_name(instance).name.to_string(),reason:"foreign declaration has no MIR; source execution uses foreign-item dispatch" } });
            continue;
        }
        if let ty::InstanceKind::Virtual(def, slot) = instance.def {
            let function_type = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
            let fn_abi = match tcx.fn_abi_of_instance(
                ty::TypingEnv::fully_monomorphized().as_query_input((instance, ty::List::empty())),
            ) {
                Ok(abi) => fn_abi_json(context, tcx, abi)?,
                Err(error) => export_failure(
                    "main::export_reachable_instances",
                    format!(
                        "{}; {}",
                        "virtual instance FnAbi query failed",
                        format!("{error:?}")
                    ),
                )?,
            };
            records.push(InstanceFact { instance_id:instance_id, instance_kind:instance_kind_json(context,tcx,instance.def)?, def_id:def_json(context,def), def_path:tcx.def_path_str(def), generic_args:generic_args_json(context,tcx,instance.args)?, data:pool_instance::InstanceData::VirtualDispatchTarget { dispatch_slot:slot,body_status:"not_applicable", virtual_identity:pool_instance::VirtualIdentity { function_type:type_json(context,tcx,function_type)?,fn_abi }, reason:"exact virtual method identity and ABI; runtime dispatch selects its concrete implementation from the actual vtable" } });
            continue;
        }
        if matches!(instance.def, ty::InstanceKind::Item(_))
            && (!has_instance_mir_source(tcx, def_id) || is_required_trait_method(tcx, def_id))
        {
            records.push(export_failure(
                "main::export_reachable_instances",
                "instance_mir_unavailable",
            )?);
            continue;
        }
        let template = tcx.instance_mir(instance.def);
        context.runtime_mir_frame_instances.insert(instance);
        let body_json = resolved_mir_body_json(tcx, template, instance, context)?;
        // Local HIR bodies own a promoted table even when empty. Imported or
        // compiler-generated MIR can lack that optional table; query it only
        // when the body actually carries a promoted reference.
        let promoted = if has_local_hir_body(tcx, def_id) || body_uses_promoted(template) {
            tcx.promoted_mir(def_id)
                .iter_enumerated()
                .map(|(index, body)| Ok(pool_instance::PromotedBody {
                    promoted_index: index.as_u32(),
                    body: resolved_mir_body_json(tcx, body, instance, context)?,
                }))
                .collect::<Result<Vec<_>, String>>()?
        } else {
            Vec::new()
        };
        let definition=def_json(context,def_id);
        let definition_path=tcx.def_path_str(def_id);
        let generic_args=generic_args_json(context,tcx,instance.args)?;
        let instance_kind=instance_kind_json(context,tcx,instance.def)?;
        records.push(InstanceFact { instance_id:instance_id, instance_kind, def_id:definition, def_path:definition_path, generic_args, data:pool_instance::InstanceData::InstanceMir { body:body_json,promoted_bodies:promoted } });
    }
    Ok::<_, String>(records)
}

// Metadata-only references must retain identity without requesting executable MIR.
struct IdentityFact {
    instance_id: u64,
    instance_kind: pool_instance::InstanceKind,
    def_id: u64,
    def_path: String,
    generic_args: Vec<pool_values::GenericArgument>,
}
impl IdentityFact {
    fn finish(self) -> pool_instance::Instance {
        pool_instance::Instance {
            instance_id: self.instance_id, instance_kind: self.instance_kind,
            def_id: self.def_id, def_path: self.def_path, generic_args: self.generic_args,
            data: pool_instance::InstanceData::IdentityOnly {
                reason: "compiler instance identity; source MIR was not demanded",
            },
        }
    }
}
#[derive(Default)]
struct IdentityDiscovery {
    events: usize,
    facts: BTreeMap<u64, IdentityFact>,
}
impl IdentityDiscovery {
    fn finish(self, context: &ExportContext<'_>) -> Vec<pool_instance::Instance> {
        self.facts.into_values().filter(|fact| {
            let instance = context.instance_ids.key(fact.instance_id as usize).unwrap();
            context.symbol_only_instances.contains(instance)
        }).map(IdentityFact::finish).collect()
    }
}
fn identity_only_instances_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut IdentityDiscovery,
) -> Result<(), String> {
    let mut seen = HashSet::new();
    let mut identities = context.instance_events[state.events..].iter().copied()
        .filter(|instance| seen.insert(*instance) && context.symbol_only_instances.contains(instance))
        .map(|instance| (context.instance_ids[&instance], instance))
        .filter(|(id, _)| !state.facts.contains_key(id))
        .collect::<Vec<_>>();
    state.events = context.instance_events.len();
    identities.sort_by_key(|(id, _)| *id);
    let facts = identities
        .into_iter()
        .map(|(id, instance)| {
            {
                Ok::<_, String>(IdentityFact { instance_id:id, instance_kind:instance_kind_json(context,tcx,instance.def)?, def_id:def_json(context,instance.def.def_id()), def_path:tcx.def_path_str(instance.def.def_id()), generic_args:generic_args_json(context,tcx,instance.args)? })
            }
        })
        .collect::<Result<Vec<_>, String>>()?;
    for fact in facts { state.facts.insert(fact.instance_id, fact); }
    Ok(())
}

// Each concrete instance owns one executable body. Normalize only its template:
// rebinding a substituted body can capture caller parameters incorrectly.
fn resolved_mir_body_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    template: &rustc_middle::mir::Body<'tcx>,
    instance: ty::Instance<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<u64, String> {
    if instance.args.has_non_region_param()
        || instance.args.has_escaping_bound_vars()
        || instance.args.has_infer()
        || instance.args.has_placeholders()
    {
        return export_failure("resolved MIR", "instance requires concrete type and const arguments");
    }
    let (id, fresh) = context.bodies.reserve(BodyKey {
        instance,
        promoted: template.source.promoted,
    });
    if !fresh {
        return Ok(id as u64);
    }
    let body = instance.try_instantiate_mir_and_normalize_erasing_regions(
        tcx, template.typing_env(tcx), ty::EarlyBinder::bind(tcx, template.clone()),
    ).map_err(|error| format!("resolved MIR: instantiation or normalization failed: {error:?}"))?;
    if body.has_non_region_param()
        || body.has_escaping_bound_vars()
        || body.has_infer()
        || body.has_placeholders()
    {
        return export_failure("resolved MIR", "body retains unresolved generic parameters");
    }
    let definition = mir_body_json(tcx, &body, instance, context, "resolved_body")?;
    context.bodies.define(id, definition);
    Ok(id as u64)
}

fn export_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    local_def_id: LocalDefId,
    context: &mut ExportContext<'tcx>,
) -> Result<BodyRoot, String> {
    let def_id = local_def_id.to_def_id();
    let body = tcx.instance_mir(ty::InstanceKind::Item(def_id));
    let instance = ty::Instance {
        def: body.source.instance,
        args: ty::GenericArgs::identity_for_item(tcx, def_id),
    };
    // Instance::mono erases lifetime parameters only. Do not fabricate type or
    // const arguments for generic roots, even when optimized MIR ignores them.
    if instance.args.has_non_region_param() {
        return unavailable_compiler_fact(
            "root requires explicit type/const instantiation; Instance::mono cannot invent arguments",
        );
    }
    let instance = ty::Instance::mono(tcx, def_id);
    context.runtime_mir_frame_instances.insert(instance);
    let entry_instance = context.register_instance(instance);
    let body_id = resolved_mir_body_json(tcx, body, instance, context)?;
    Ok(BodyRoot { body:body_id,
        entry_instance,
        def_path:tcx.def_path_str(def_id), def_id:def_json(context,def_id), is_static:tcx.is_static(def_id),
        thread_local_static:tcx.is_thread_local_static(def_id),
        promoted_bodies:tcx.promoted_mir(def_id).iter_enumerated().map(|(index,promoted)|Ok(PromotedRoot {
            promoted_index:index.as_u32(),
            body:resolved_mir_body_json(tcx, promoted, instance, context)?,
        })).collect::<Result<Vec<_>,String>>()?,
    })
}

fn mir_body_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    instance: ty::Instance<'tcx>,
    context: &mut ExportContext<'tcx>,
    role: &'static str,
) -> Result<pool_body::Body, String> {
    let previous = if context.vtable_diagnostics.enabled() {
        context
            .vtable_diagnostics
            .body
            .replace(vtable_diagnostics::BodyOrigin {
                role,
                def_id: body.source.def_id(),
                promoted: body.source.promoted.map(|p| p.as_u32()),
                phase: format!("{:?}", body.phase),
            })
    } else {
        None
    };
    if body.coroutine.is_some() {
        export_failure::<()>("MIR", "coroutine layout serialization is not implemented")?;
    }
    intrinsic_value_queries::collect_spans(tcx, context, body);
    let result = pool_body::Body {
        instance_id: context.register_metadata_instance(instance),
        source_instance_kind: instance_kind_json(context, tcx, body.source.instance)?,
        preamble_def_span: span_json(context, tcx, tcx.def_span(body.source.def_id())),
        backtrace_spans: backtrace_spans_json(context, tcx, body),
        source_def_id: def_json(context, body.source.def_id()),
        source_promoted: body.source.promoted.map(|value| value.as_u32()),
        phase: mir_phase_json(body.phase),
        pass_count: body.pass_count,
        injection_phase: body.injection_phase.map(mir_phase_json),
        tainted_by_errors: body.tainted_by_errors.map(|value| pool_values::DebugPayload::new(&value)),
        arg_count: body.arg_count,
        spread_arg: body.spread_arg.map(|local| local.as_u32()),
        span: span_json(context, tcx, body.span),
        locals: body.local_decls.iter_enumerated().map(|(local, decl)| Ok(pool_body::Local {
            local: local.as_u32(),
            mutability: match decl.mutability { rustc_ast::Mutability::Mut => pool_body::Mutability::Mutable, rustc_ast::Mutability::Not => pool_body::Mutability::Immutable },
            r#type: type_json(context, tcx, decl.ty)?,
            layout: layout_json(context, tcx, decl.ty)?,
            source_info: source_info_json(context, tcx, decl.source_info),
            local_info: pool_body::DebugPayload::new(&decl.local_info),
        })).collect::<Result<Vec<_>, String>>()?,
        basic_blocks: body.basic_blocks.iter_enumerated().map(|(bb, data)| Ok(pool_body::BasicBlock {
            block: bb.as_u32(),
            is_cleanup: data.is_cleanup,
            statements: data.statements.iter().map(|statement| Ok(pool_body::Statement {
                source_info: source_info_json(context, tcx, statement.source_info),
                kind: statement_json(context, tcx, body, &statement.kind)?,
            })).collect::<Result<Vec<_>, String>>()?,
            terminator: data.terminator.as_ref().map(|term| Ok::<_, String>(pool_body::Terminator {
                source_info: source_info_json(context, tcx, term.source_info),
                kind: terminator_json(context, tcx, body, &term.kind)?,
            })).transpose()?,
        })).collect::<Result<Vec<_>, String>>()?,
        source_scopes: body.source_scopes.iter_enumerated().map(|(scope, data)| Ok(pool_body::SourceScope {
            scope: scope.as_u32(),
            parent: data.parent_scope.map(|parent| parent.as_u32()),
            span: span_json(context, tcx, data.span),
            inlined: data.inlined.map(|(instance, callsite)| pool_body::InlinedScope {
                instance_id: context.register_metadata_instance(instance),
                callsite_span: span_json(context, tcx, callsite),
                requires_caller_location: instance.def.requires_caller_location(tcx),
            }),
            inlined_parent_scope: data.inlined_parent_scope.map(|parent| parent.as_u32()),
            local_data: pool_body::DebugPayload::new(&data.local_data),
        })).collect::<Result<Vec<_>, String>>()?,
        var_debug_info: body.var_debug_info.iter().map(pool_values::DebugPayload::new).collect(),
        mentioned_items: body.mentioned_items.as_ref().map(pool_values::DebugPayload::new),
        required_consts: body.required_consts.as_ref().ok_or_else(||
            "resolved MIR: compiler body has no required_consts list".to_owned())?
            .iter().map(|v| const_operand_json(context, tcx, body, v))
            .collect::<Result<Vec<_>, String>>()?,
        user_type_annotations: pool_values::DebugPayload::new(&body.user_type_annotations),
        coroutine_info: None,
    };
    context.vtable_diagnostics.body = previous;
    Ok::<_, String>(result)
}

fn source_info_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, info: rustc_middle::mir::SourceInfo) -> pool_body::SourceInfo {
    pool_body::SourceInfo { span: span_json(context, tcx, info.span), scope: info.scope.as_u32() }
}

fn span_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, span: rustc_span::Span) -> u64 {
    let (id, fresh) = context.spans.reserve(span);
    if fresh {
        let map=tcx.sess.source_map(); let start=map.lookup_char_pos(span.lo()); let end=map.lookup_char_pos(span.hi());
        context.spans.define(id,pool_values::Span { is_dummy:span.is_dummy(),lo:span.lo().0,hi:span.hi().0,ctxt:pool_values::DebugPayload::new(&span.ctxt()),file:context.files.intern(format!("{:?}", start.file.name)),start:pool_values::Position {line:start.line,column:start.col.to_usize()},end:pool_values::Position {line:end.line,column:end.col.to_usize()} });
    }
    id as u64
}



fn type_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<u64, String> {
    // rustc layout is region-insensitive. Query the exact region-erased form
    // for late-bound region types while retaining the source Ty and its Binder
    // graph as the exported type identity and signature evidence.
    let query_ty = if ty.has_escaping_bound_vars()
        && !ty.has_non_region_param()
        && !ty.has_infer()
        && !ty.has_placeholders()
        && !ty.references_error()
    {
        ty::fold_regions(tcx, ty, |_, _| tcx.lifetimes.re_erased)
    } else {
        ty
    };
    type_json_with_query(context, tcx, ty, query_ty)
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
) -> Result<u64, String> {
    // Signature-bound types are metadata inside their Binder, not runtime
    // query inputs. The instantiated signature registers its closed types.
    if context.runtime_type_query_suppression == 0 && !ty.has_escaping_bound_vars() {
        context.runtime_type_query_demands.insert(ty);
    }
    let id = context.type_id(ty);
    if context.type_ids.definition(id).is_some() || context.type_nodes_in_progress.contains(&ty) {
        return Ok(id);
    }
    context.type_nodes_in_progress.insert(ty);
    let node = type_json_inner(context, tcx, ty, query_ty)?;
    context.type_nodes_in_progress.remove(&ty);
    context.type_ids.define(id as usize, node);
    Ok(id)
}

/// Serialize a type produced only as a compiler runtime-query result. Its
/// graph still gets exported, but it is not a new source-demand query key.
fn query_generated_type_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<u64, String> {
    context.runtime_type_query_suppression += 1;
    let result = type_json(context, tcx, ty)?;
    context.runtime_type_query_suppression -= 1;
    Ok::<_, String>(result)
}

fn compiler_fact<T: serde::Serialize>(value: T) -> T { value }
fn unavailable_compiler_fact<T>(reason: &str) -> Result<T, String> {
    export_failure("main::unavailable_compiler_fact", reason)
}

// Query keys are exact interned input types under this explicit typing_env.
// Symbolic caller parameters are not queried as though they were monomorphic.
fn pattern_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    pattern: ty::Pattern<'tcx>,
) -> Result<pool_type::Pattern, String> {
    use pool_type::Pattern;
    Ok(match *pattern.0 {
        ty::PatternKind::Range { start, end } => Pattern::Range {
            start: const_type_json(context, tcx, start)?,
            end: const_type_json(context, tcx, end)?,
        },
        ty::PatternKind::Or(patterns) => Pattern::Or {
            patterns: patterns
                .iter()
                .map(|p| pattern_json(context, tcx, p))
                .collect::<Result<_, _>>()?,
        },
        ty::PatternKind::NotNull => Pattern::NotNull,
    })
}

/// Guard the private fast path in pinned rustc_middle/ty/util.rs::is_trivially_unpin.
/// The answers still come from rustc's public is_unpin/is_unsafe_unpin methods;
/// these shapes ensure neither method requires a missing trait language item.
fn unpin_query_needs_no_lang_item(input: ty::Ty<'_>) -> bool {
    match input.kind() {
        ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Bool
        | ty::Char
        | ty::Str
        | ty::Never
        | ty::Ref(..)
        | ty::RawPtr(..)
        | ty::FnDef(..)
        | ty::Error(_)
        | ty::FnPtr(..) => true,
        ty::Tuple(fields) => fields.iter().all(unpin_query_needs_no_lang_item),
        ty::Pat(input, _) | ty::Slice(input) | ty::Array(input, _) => {
            unpin_query_needs_no_lang_item(*input)
        }
        _ => false,
    }
}

fn type_compiler_facts_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
) -> Result<pool_type::CompilerFacts, String> {
    use pool_type::*;
    let env = ty::TypingEnv::fully_monomorphized();
    let closed = !input.has_non_region_param()
        && !input.has_escaping_bound_vars()
        && !input.has_infer()
        && !input.has_placeholders()
        && !input.references_error();
    if !closed {
        return export_failure(
            "type queries",
            "type queries require a closed monomorphic typing environment",
        );
    }
    let normalized = tcx
        .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(input))
        .map_err(|e| format!("type normalization failed: {e:?}"))?;
    let missing = || "required compiler trait language item is missing".to_owned();
    let is_freeze = if normalized.is_trivially_freeze()
        || tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::Freeze)
            .is_some()
    {
        normalized.is_freeze(tcx, env)
    } else {
        return Err(missing());
    };
    let is_unpin = if unpin_query_needs_no_lang_item(normalized)
        || tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::Unpin)
            .is_some()
    {
        normalized.is_unpin(tcx, env)
    } else {
        return Err(missing());
    };
    let is_unsafe_unpin = if unpin_query_needs_no_lang_item(normalized)
        || tcx
            .lang_items()
            .get(rustc_attr_ir::LangItem::UnsafeUnpin)
            .is_some()
    {
        normalized.is_unsafe_unpin(tcx, env)
    } else {
        return Err(missing());
    };
    let boolean_queries = BooleanQueries {
        is_unsafe_cell: matches!(input.kind(),ty::Adt(d,_) if d.is_unsafe_cell()),
        has_erasable_regions: input.has_erasable_regions(),
        is_c_void: input.is_c_void(tcx),
        is_simd: input.is_simd(),
        is_box: input.is_box(),
        is_global_box: input.is_box_global(tcx),
        is_dynamic: matches!(input.kind(), ty::Dynamic(..)),
        is_too_generic: matches!(
            input.kind(),
            ty::Param(..)
                | ty::Alias(..)
                | ty::Bound(..)
                | ty::Placeholder(..)
                | ty::Infer(..)
                | ty::Error(..)
        ),
        is_monomorphic: closed,
        is_monomorphic_enough: !input.has_param(),
        is_like_maybe_dangling: input.is_like_maybe_dangling(),
        is_freeze,
        is_unpin,
        is_unsafe_unpin,
        needs_drop: normalized.needs_drop(tcx, env),
        opsem_inhabited: normalized.is_opsem_inhabited(tcx, env),
        is_sized: normalized.is_sized(tcx, env),
    };
    let discriminant_type = discriminant_type_fact_json(context, tcx, normalized)?;
    let normalized_id = type_json(context, tcx, normalized)?;
    let builtin_deref_explicit = input
        .builtin_deref(true)
        .map(|t| type_json(context, tcx, t))
        .transpose()?;
    let builtin_deref_implicit = input
        .builtin_deref(false)
        .map(|t| type_json(context, tcx, t))
        .transpose()?;
    let boxed_type = input
        .boxed_ty()
        .map(|t| type_json(context, tcx, t))
        .transpose()?;
    let unsafe_binder_erased = match input.kind() {
        ty::UnsafeBinder(b) => Some(type_json(
            context,
            tcx,
            tcx.instantiate_bound_regions_with_erased((*b).into()),
        )?),
        _ => None,
    };
    let tail = tcx.struct_tail_for_codegen(normalized, env);
    if matches!(tail.kind(), ty::UnsafeBinder(..)) {
        return export_failure(
            "pointer metadata",
            "rustc ptr_metadata_ty_or_tail does not implement UnsafeBinder",
        );
    }
    let metadata = normalized
        .ptr_metadata_ty_or_tail(tcx, |t| tcx.normalize_erasing_regions(env, t))
        .map_err(|_| "rustc could not determine pointer metadata type".to_owned())?;
    let type_queries = TypeQueries {
        discriminant_type,
        normalized: normalized_id,
        builtin_deref_explicit,
        builtin_deref_implicit,
        boxed_type,
        unsafe_binder_erased,
        metadata_tail: type_json(context, tcx, tail)?,
        pointer_metadata_type: type_json(context, tcx, metadata)?,
    };
    let capture_names = match input.kind() {
        ty::Closure(def, _) | ty::CoroutineClosure(def, _) | ty::Coroutine(def, _) => Some(
            def.as_local()
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
                        .collect()
                })
                .unwrap_or_default(),
        ),
        _ => None,
    };
    let adt = if let ty::Adt(def, _) = input.kind() {
        Some(AdtFacts {
            definition: def_json(context, def.did()),
            item_name: tcx.item_name(def.did()).as_str().to_owned(),
            nonnull_optimization_guaranteed: rustc_attr_ir::find_attr!(
                tcx,
                def.did(),
                RustcNonnullOptimizationGuaranteed
            ),
        })
    } else {
        None
    };
    let simd_size_and_type = if input.is_simd() {
        let (count, element) = normalized.simd_size_and_type(tcx);
        Some(Simd {
            count: count as u64,
            element: type_json(context, tcx, element)?,
        })
    } else {
        None
    };
    Ok(CompilerFacts {
        typing_env: "fully_monomorphized",
        boolean_queries,
        type_queries,
        adt,
        capture_names,
        simd_size_and_type,
        discriminants: discriminant_facts_json(context, tcx, normalized)?,
        projection_queries: projection_queries::export(tcx, context, input)?,
        definition: match input.kind() {
            ty::Adt(def, _) => Some(def_json(context, def.did())),
            ty::FnDef(d, _)
            | ty::Closure(d, _)
            | ty::CoroutineClosure(d, _)
            | ty::Coroutine(d, _) => Some(def_json(context, *d)),
            _ => None,
        },
        type_id_hash: if input.has_erasable_regions() {
            None
        } else {
            Some(tcx.type_id_hash(input).as_u128().to_string())
        },
    })
}


fn type_json_inner<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
    query_ty: ty::Ty<'tcx>,
) -> Result<pool_type::Type, String> {
    use pool_type::*;
    let id = context.type_id(input);
    let shape = match *input.kind() {
        ty::Bool => Shape::Bool,
        ty::Char => Shape::Char,
        ty::Int(kind) => Shape::Int {
            signed_kind: kind.name_str(),
        },
        ty::Uint(kind) => Shape::Uint {
            unsigned_kind: kind.name_str(),
        },
        ty::Float(kind) => Shape::Float {
            float_kind: kind.name_str(),
        },
        ty::Adt(def, args) => {
            let adt = tcx.adt_def(def.did());
            Shape::Adt {
                def_id: def_json(context, def.did()),
                def_path: tcx.def_path_str(def.did()),
                adt_kind: match adt.adt_kind() {
                    ty::AdtKind::Struct => "struct",
                    ty::AdtKind::Union => "union",
                    ty::AdtKind::Enum => "enum",
                },
                representation: repr_options_json(&adt.repr()),
                generic_args: generic_args_json_inner(context, tcx, args)?,
                variants: adt
                    .variants()
                    .iter_enumerated()
                    .map(|(index, v)| {
                        Ok(Variant {
                            index: index.as_u32(),
                            name: v.name.as_str().to_owned(),
                            fields: v
                                .fields
                                .iter_enumerated()
                                .map(|(i, f)| {
                                    Ok(Field {
                                        index: i.as_u32(),
                                        name: f.name.as_str().to_owned(),
                                        ty: type_json(
                                            context,
                                            tcx,
                                            f.ty(tcx, args).skip_normalization(),
                                        )?,
                                    })
                                })
                                .collect::<Result<_, String>>()?,
                        })
                    })
                    .collect::<Result<_, String>>()?,
            }
        }
        ty::Foreign(def) => Shape::Foreign {
            def_id: def_json(context, def),
            def_path: tcx.def_path_str(def),
        },
        ty::Str => Shape::Str,
        ty::Array(element, length) => {
            let element_id = type_json(context, tcx, element)?;
            let length_id = const_type_json(context, tcx, length)?;
            let count = tcx
                .try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    ty::Unnormalized::new_wip(length),
                )
                .map_err(|e| format!("array length normalization failed: {e:?}"))?
                .try_to_target_usize(tcx)
                .ok_or_else(|| {
                    "closed array length did not normalize to target usize".to_owned()
                })?;
            Shape::Array {
                element: element_id,
                length: length_id,
                constructor_identity: ArrayIdentity {
                    count,
                    canonical_value_constructor: input == ty::Ty::new_array(tcx, element, count),
                },
            }
        }
        ty::Pat(base, pattern) => Shape::PatternType {
            base: type_json(context, tcx, base)?,
            pattern: pattern_json(context, tcx, pattern)?,
        },
        ty::Slice(element) => Shape::Slice {
            element: type_json(context, tcx, element)?,
        },
        ty::RawPtr(pointee, mutability) => Shape::RawPointer {
            mutability: mutability_json(mutability),
            pointee: type_json(context, tcx, pointee)?,
        },
        ty::Ref(region, pointee, mutability) => Shape::Reference {
            region: region_json(context, tcx, region)?,
            mutability: mutability_json(mutability),
            pointee: type_json(context, tcx, pointee)?,
        },
        ty::FnDef(def, args) => {
            let signature = tcx
                .fn_sig(def)
                .instantiate(tcx, args.skip_binder())
                .skip_normalization();
            let query_signature = tcx.instantiate_bound_regions_with_erased(signature);
            Shape::FunctionDefinition {
                def_id: def_json(context, def),
                def_path: tcx.def_path_str(def),
                generic_args: generic_args_json_inner(context, tcx, args.skip_binder())?,
                signature: fn_sig_json_with_query(
                    context,
                    tcx,
                    signature.skip_binder(),
                    query_signature,
                )?,
                signature_bound_variables: signature
                    .bound_vars()
                    .iter()
                    .map(|b| bound_variable_json(context, tcx, b))
                    .collect(),
            }
        }
        ty::FnPtr(signature, header) => {
            let signature = signature.with(header);
            let query_signature = tcx.instantiate_bound_regions_with_erased(signature);
            Shape::FunctionPointer {
                signature: fn_sig_json_with_query(
                    context,
                    tcx,
                    signature.skip_binder(),
                    query_signature,
                )?,
                signature_bound_variables: signature
                    .bound_vars()
                    .iter()
                    .map(|b| bound_variable_json(context, tcx, b))
                    .collect(),
            }
        }
        ty::UnsafeBinder(inner) => Shape::UnsafeBinder {
            inner: type_json(context, tcx, inner.skip_binder())?,
            bound_variables: inner
                .bound_vars()
                .iter()
                .map(|b| bound_variable_json(context, tcx, b))
                .collect(),
        },
        ty::Dynamic(predicates, region) => {
            let principal_predicate = predicates
                .principal()
                .map(|p| {
                    existential_predicate_json(
                        context,
                        tcx,
                        p.map_bound(ty::ExistentialPredicate::Trait),
                    )
                })
                .transpose()?;
            let predicates = predicates
                .iter()
                .map(|p| existential_predicate_json(context, tcx, p))
                .collect::<Result<_, String>>()?;
            Shape::DynamicTraitObject {
                region: region_json(context, tcx, region)?,
                predicates,
                principal_predicate,
            }
        }
        ty::Closure(def, args) => Shape::Closure {
            def_id: def_json(context, def),
            def_path: tcx.def_path_str(def),
            generic_args: generic_args_json_inner(context, tcx, args)?,
            upvar_count: args.as_closure().upvar_tys().len(),
        },
        ty::CoroutineClosure(def, args) => Shape::CoroutineClosure {
            def_id: def_json(context, def),
            def_path: tcx.def_path_str(def),
            generic_args: generic_args_json_inner(context, tcx, args)?,
        },
        ty::Coroutine(def, args) => Shape::Coroutine {
            def_id: def_json(context, def),
            def_path: tcx.def_path_str(def),
            generic_args: generic_args_json_inner(context, tcx, args)?,
        },
        ty::CoroutineWitness(def, args) => {
            return export_failure(
                "coroutine witness",
                format!("{}: {args:?}", tcx.def_path_str(def)),
            );
        }
        ty::Never => Shape::Never,
        ty::Tuple(types) => Shape::Tuple {
            elements: types
                .iter()
                .map(|t| type_json(context, tcx, t))
                .collect::<Result<_, _>>()?,
        },
        ty::Alias(_, alias) => Shape::Alias {
            alias_payload: alias_payload_json(context, tcx, alias.kind),
            def_id: alias_def_id_json(context, alias.kind),
            generic_args: generic_args_json_inner(context, tcx, alias.args)?,
        },
        ty::Param(param) => {
            return export_failure("uninstantiated type parameter", format!("{param:?}"));
        }
        ty::Bound(d, b) => return export_failure("bound type", format!("{d:?}: {b:?}")),
        ty::Placeholder(p) => return export_failure("placeholder type", format!("{p:?}")),
        ty::Infer(i) => return export_failure("type inference", format!("{i:?}")),
        ty::Error(e) => {
            return export_failure("main::type_json_inner", format!("error_type; {e:?}"));
        }
    };
    Ok(Type {
        type_id: id,
        display: input.to_string(),
        shape,
        layout: layout_json(context, tcx, query_ty)?,
        layout_query_input_type: if query_ty == input {
            None
        } else {
            Some(query_generated_type_json(context, tcx, query_ty)?)
        },
        compiler_facts: type_compiler_facts_json(context, tcx, query_ty)?,
    })
}

fn alias_payload_json(
    context: &mut ExportContext<'_>,
    tcx: TyCtxt<'_>,
    kind: ty::AliasTyKind<'_>,
) -> pool_type::Alias {
    use ty::AliasTyKind as A;
    let (name, def) = match kind {
        A::Projection { def_id } => ("Projection", def_id),
        A::Inherent { def_id } => ("Inherent", def_id),
        A::Opaque { def_id } => ("Opaque", def_id),
        A::Free { def_id } => ("Free", def_id),
    };
    pool_type::Alias {
        kind: name,
        def_id: def_json(context, def),
        def_path: tcx.def_path_str(def),
    }
}

fn alias_def_id_json(context: &mut ExportContext<'_>, kind: ty::AliasTyKind<'_>) -> u64 {
    use ty::AliasTyKind as A;
    let def = match kind {
        A::Projection { def_id }
        | A::Inherent { def_id }
        | A::Opaque { def_id }
        | A::Free { def_id } => def_id,
    };
    def_json(context, def)
}

fn repr_options_json(repr: &rustc_abi::ReprOptions) -> pool_type::Representation {
    use pool_type::*;
    Representation {
        integer: repr.int.map(|value| match value {
            rustc_abi::IntegerType::Pointer(signed) => {
                RepresentationInteger::PointerSized { signed }
            }
            rustc_abi::IntegerType::Fixed(integer, signed) => RepresentationInteger::Fixed {
                integer_kind: integer.int_ty_str(),
                size_bits: integer.size().bits(),
                signed,
            },
        }),
        align_bytes: repr.align.map(|v| v.bytes()),
        pack_bytes: repr.pack.map(|v| v.bytes()),
        flags_bits: repr.flags.bits(),
        scalable_element: repr.scalable.map(|v| match v {
            rustc_abi::ScalableElt::ElementCount(count) => ScalableElement::ElementCount {
                count: count as u64,
            },
            rustc_abi::ScalableElt::Container => ScalableElement::Container,
        }),
        field_shuffle_seed: repr.field_shuffle_seed.as_u64(),
    }
}


fn generic_args_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> Result<Vec<pool_values::GenericArgument>, String> { generic_args_json_inner(context,tcx,args) }
fn generic_args_json_inner<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> Result<Vec<pool_values::GenericArgument>, String> {
    args.iter().map(|arg| Ok(match arg.kind() {
        ty::GenericArgKind::Type(ty)=>pool_values::GenericArgument::Type(type_json(context,tcx,ty)?),
        ty::GenericArgKind::Lifetime(region)=>pool_values::GenericArgument::Lifetime(region_json(context,tcx,region)?),
        ty::GenericArgKind::Const(value)=>pool_values::GenericArgument::Const(const_type_json(context,tcx,value)?),
    })).collect()
}

fn const_type_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, value: ty::Const<'tcx>) -> Result<u64, String> {
    let (id,fresh)=context.type_constants.reserve(value);
    if fresh { let definition=const_type_definition_json(context,tcx,value)?; context.type_constants.define(id,definition); }
    Ok(id as u64)
}
fn const_type_definition_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, value: ty::Const<'tcx>) -> Result<pool_values::TypeConstant,String> {
    use ty::ConstKind as C; use pool_values::TypeConstant as O;
    Ok(match value.kind() {
        C::Value(c)=>O::Value {ty:type_json(context,tcx,c.ty)?,value:valtree_json(context,tcx,c.valtree)?},
        C::Alias(r,a)=>{
            let (alias_kind,def)=match a.kind {ty::AliasConstKind::Projection {def_id}=>("projection",def_id),ty::AliasConstKind::InherentSelf {def_id}=>("inherent_self",def_id),ty::AliasConstKind::InherentImpl {def_id}=>("inherent_impl",def_id),ty::AliasConstKind::Free {def_id}=>("free",def_id),ty::AliasConstKind::Anon {def_id}=>("anonymous",def_id)};
            O::Alias {rigidity:match r {ty::IsRigid::Yes=>"rigid",ty::IsRigid::No=>"not_rigid"},alias_kind,def_id:def_json(context,def),def_path:tcx.def_path_str(def),generic_args:generic_args_json_inner(context,tcx,a.args)?}
        },
        C::Expr(e)=>{
            let (expression_kind,operator)=match e.kind {ty::ExprKind::Binop(op)=>("binary_operator",Some(binop_name(op))),ty::ExprKind::UnOp(op)=>("unary_operator",Some(unop_name(op))),ty::ExprKind::FunctionCall=>("function_call",None),ty::ExprKind::Cast(c)=>("cast",Some(match c {ty::abstract_const::CastKind::As=>"as",ty::abstract_const::CastKind::Use=>"use"}))};
            O::Expression {expression_kind,operator,arguments:generic_args_json_inner(context,tcx,e.args())?}
        },
        C::Param(p)=>return export_failure("constant",format!("{p:?}")),
        C::Bound(d,b)=>return export_failure("bound constant",format!("{d:?}: {b:?}")),
        C::Placeholder(p)=>return export_failure("constant",format!("{p:?}")),
        C::Infer(i)=>return export_failure("constant",format!("{i:?}")),
        C::Error(_)=>return export_failure("main::const_type_json","error"),
    })
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

fn valtree_json<'tcx>(context: &mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,value:ty::ValTree<'tcx>)->Result<pool_values::ValTree,String>{
    Ok(match &*value {
        ty::ValTreeKind::Leaf(s)=>pool_values::ValTree::Leaf {size_bytes:s.size().bytes(),bits_unsigned:s.to_bits_unchecked().to_string()},
        ty::ValTreeKind::Branch(v)=>pool_values::ValTree::Branch {elements:v.iter().map(|c|const_type_json(context,tcx,c)).collect::<Result<_,_>>()?},
    })
}

fn fn_sig_json_inner<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    sig: ty::FnSig<'tcx>,
) -> Result<pool_type::FunctionSignature, String> {
    fn_sig_json_with_query(context, tcx, sig, sig)
}

fn fn_sig_json_with_query<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    sig: ty::FnSig<'tcx>,
    query_sig: ty::FnSig<'tcx>,
) -> Result<pool_type::FunctionSignature, String> {
    Ok(pool_type::FunctionSignature {
        inputs: sig
            .inputs()
            .iter()
            .zip(query_sig.inputs())
            .map(|(input, query)| type_json_with_query(context, tcx, *input, *query))
            .collect::<Result<_, _>>()?,
        output: type_json_with_query(context, tcx, sig.output(), query_sig.output())?,
        safety: safety_json(sig.safety()),
        abi: extern_abi_json(sig.abi()),
        c_variadic: sig.c_variadic(),
    })
}

fn layout_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<u64, String> {
    if ty.has_escaping_bound_vars() {
        return Ok(export_failure(
            "main::layout_json",
            format!(
                "{}; {}",
                "type contains escaping bound variables; the pinned layout query may panic on this non-monomorphic input",
                "layout"
            ),
        )?);
    }
    if ty.has_non_region_param() {
        return Ok(export_failure(
            "main::layout_json",
            format!(
                "{}; {}",
                "type still contains non-region generic parameters", "layout"
            ),
        )?);
    }
    if ty.has_infer() || ty.has_placeholders() {
        return Ok(export_failure(
            "main::layout_json",
            format!(
                "{}; {}",
                "type still contains inference or placeholder variables", "layout"
            ),
        )?);
    }
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
    Ok::<_, String>(match tcx.layout_of(typing_env.as_query_input(ty)) {
        Ok(layout) => layout_value_json(context, tcx, layout),
        Err(error) => export_failure("layout query", format!("{ty:?}: {error:?}"))?,
    })
}

// Preserve queried TyAndLayout, including field-specific and uninhabited
// variant layouts which cannot be replaced by layout_of(result.ty).
fn layout_value_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    layout: rustc_abi::TyAndLayout<'tcx, ty::Ty<'tcx>>,
) -> u64 {
    let (id, fresh) = context.layouts.reserve(layout);
    if !fresh {
        return id as u64;
    }
    let value = pool_layout::Layout::new(tcx, layout);
    context.layouts.define(id, value);
    id as u64
}

fn statement_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    kind: &rustc_middle::mir::StatementKind<'tcx>,
) -> Result<pool_body::StatementKind, String> {
    use rustc_middle::mir::StatementKind as S;
    use pool_body::{StatementKind as T, Intrinsic as I};
    Ok::<_, String>(match kind {
        S::Assign(pair) => {
            T::Assign { place: place_json(context, tcx, body, &pair.0)?, rvalue: rvalue_json(context, tcx, body, &pair.1)? }
        }
        S::FakeRead(pair) => {
            T::FakeRead { cause: fake_read_cause_json(context, pair.0), place: place_json(context, tcx, body, &pair.1)? }
        }
        S::SetDiscriminant {
            place,
            variant_index,
        } => {
            T::SetDiscriminant { place: place_json(context, tcx, body, place)?, variant_index: variant_index.as_u32() }
        }
        S::StorageLive(local) => {
            T::StorageLive { local: local.as_u32() }
        }
        S::StorageDead(local) => {
            T::StorageDead { local: local.as_u32() }
        }
        S::PlaceMention(place) => {
            T::PlaceMention { place: place_json(context, tcx, body, place)? }
        }
        S::AscribeUserType(pair, variance) => {
            T::AscribeUserType { execution: "no_op", place: place_json(context, tcx, body, &pair.0)?, user_type_projection: user_type_projection_json(&pair.1), variance: variance_json(*variance) }
        }
        S::Coverage(value) => {
            T::Coverage { execution: "no_op", coverage: coverage_kind_json(context, value) }
        }
        S::Intrinsic(intrinsic) => match &**intrinsic {
            rustc_middle::mir::NonDivergingIntrinsic::Assume(value) => {
                T::Intrinsic { intrinsic: I::Assume { value: operand_json(context, tcx, body, value)? } }
            }
            rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                T::Intrinsic { intrinsic: I::CopyNonOverlapping { src: operand_json(context, tcx, body, &copy.src)?, dst: operand_json(context, tcx, body, &copy.dst)?, count: operand_json(context, tcx, body, &copy.count)? } }
            }
        },
        S::ConstEvalCounter => T::ConstEvalCounter,
        S::Nop => T::Nop,
        S::BackwardIncompatibleDropHint { place, reason } => {
            let reason = match reason { rustc_middle::mir::BackwardIncompatibleDropReason::Edition2024 => pool_body::DropHintReason::Edition2024 };
            T::BackwardIncompatibleDropHint { place: place_json(context, tcx, body, place)?, reason }
        }
    })
}

fn variance_json(variance: ty::Variance) -> pool_body::Variance {
    use ty::Variance as V;
    use pool_body::Variance as S;
    match variance { V::Covariant => S::Covariant, V::Contravariant => S::Contravariant,
        V::Invariant => S::Invariant, V::Bivariant => S::Bivariant }
}

fn user_type_projection_json(projection: &rustc_middle::mir::UserTypeProjection) -> pool_body::UserTypeProjection {
    use rustc_middle::mir::ProjectionKind as P;
    use pool_body::UserProjection as U;
    pool_body::UserTypeProjection {
        base_index: projection.base.as_u32(),
        projections: projection.projs.iter().map(|projection| match *projection {
            P::Deref => U::Deref,
            P::Field(index, ()) => U::Field { index: index.as_u32() },
            P::Index(()) => U::Index,
            P::ConstantIndex { offset, min_length, from_end } => U::ConstantIndex { offset, min_length, from_end },
            P::Subslice { from, to, from_end } => U::Subslice { from, to, from_end },
            P::Downcast(name, variant) => U::Downcast { name: name.map(|n| n.as_str().to_owned()), variant_index: variant.as_u32() },
            P::OpaqueCast(()) => U::OpaqueCast,
            P::UnwrapUnsafeBinder(()) => U::UnwrapUnsafeBinder,
            P::PhantomDeref => U::PhantomDeref,
        }).collect(),
    }
}

fn coverage_kind_json(context: &mut ExportContext<'_>, kind: &rustc_middle::mir::coverage::CoverageKind) -> pool_body::Coverage {
    use rustc_middle::mir::coverage::{CoverageKind as C, PointKind};
    use pool_body::{Coverage as S, CoveragePoint as P};
    match kind {
        C::Point { point_kind, hir_id } => S::Point {
            point_kind: match point_kind { PointKind::Expr => P::Expr,
                PointKind::ImplicitElse => P::ImplicitElse, PointKind::FunctionEnd => P::FunctionEnd },
            hir_id: pool_body::HirId { owner_def_id: def_json(context, hir_id.owner.def_id.to_def_id()), local_id: hir_id.local_id.as_u32() },
        },
        C::BlockMarker { id } => S::BlockMarker { id: id.as_u32() },
        C::VirtualCounter { bcb } => S::VirtualCounter { bcb: bcb.as_u32() },
    }
}

fn terminator_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    kind: &rustc_middle::mir::TerminatorKind<'tcx>,
) -> Result<pool_body::TerminatorKind, String> {
    use rustc_middle::mir::TerminatorKind as T;
    use pool_body::TerminatorKind as S;
    if let Some(rustc_middle::mir::UnwindAction::Terminate(reason)) = kind.unwind() {
        panic_queries::register_unwind_termination(tcx, context, *reason)?;
    }
    Ok::<_, String>(match kind {
        T::Goto {
            target,
            loop_hint_attrs,
        } => {
            let hints = loop_hint_attrs
                .iter()
                .map(|hint| match hint {
                    rustc_attr_ir::UnrollAttr::Hint => pool_body::LoopHint::Hint,
                    rustc_attr_ir::UnrollAttr::Full => pool_body::LoopHint::Full,
                    rustc_attr_ir::UnrollAttr::Never => pool_body::LoopHint::Never,
                    rustc_attr_ir::UnrollAttr::Count(count) => {
                        pool_body::LoopHint::Count { count: *count }
                    }
                })
                .collect::<Vec<_>>();
            S::Goto { target: target.as_u32(), loop_hints: hints }
        }
        T::SwitchInt { discr, targets } => {
            S::SwitchInt { discriminant: operand_json(context, tcx, body, discr)?, targets: targets.iter().map(|(value, block)| pool_body::SwitchTarget { value: value.to_string(), target: block.as_u32() }).collect(), otherwise: targets.otherwise().as_u32() }
        }
        T::UnwindResume => S::UnwindResume,
        T::UnwindTerminate(reason) => {
            panic_queries::register_unwind_termination(tcx, context, *reason)?;
            S::UnwindTerminate { reason: unwind_terminate_reason_json(*reason) }
        }
        T::Return => S::Return,
        T::Unreachable => S::Unreachable,
        T::Drop {
            place,
            target,
            unwind,
            replace,
            drop,
        } => {
            if tcx
                .lang_items()
                .get(rustc_attr_ir::LangItem::DropGlue)
                .is_none()
            {
                export_failure::<()>("Drop", "required drop_in_place language item is missing")?;
            }
            if drop.is_some() {
                export_failure::<()>("Drop", "async Drop requires expansion before export")?;
            }
            S::Drop { place: place_json(context, tcx, body, place)?, target: target.as_u32(), unwind: unwind_json(*unwind), replace: *replace, async_drop: drop.map(|bb| bb.as_u32()) }
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
            S::Call { function: operand_json(context, tcx, body, func)?, resolution: resolve_callee_json(context, tcx, body, func, args, destination.ty(body, tcx).ty)?, args: args.iter().map(|arg| Ok(pool_body::CallArgument { operand: operand_json(context, tcx, body, &arg.node)?, span: span_json(context, tcx, arg.span) })).collect::<Result<Vec<_>, String>>()?, destination: place_json(context, tcx, body, destination)?, target: target.map(|bb| bb.as_u32()), unwind: unwind_json(*unwind), call_source: pool_body::CallSource { kind: call_source_name(*call_source) }, function_span: span_json(context, tcx, *fn_span) }
        }
        T::TailCall {
            func,
            args,
            fn_span,
        } => {
            S::TailCall { function: operand_json(context, tcx, body, func)?, resolution: resolve_callee_json(context, tcx, body, func, args, body.local_decls[rustc_middle::mir::RETURN_PLACE].ty)?, args: args.iter().map(|arg| Ok(pool_body::CallArgument { operand: operand_json(context, tcx, body, &arg.node)?, span: span_json(context, tcx, arg.span) })).collect::<Result<Vec<_>, String>>()?, function_span: span_json(context, tcx, *fn_span) }
        }
        T::Assert {
            cond,
            expected,
            msg,
            target,
            unwind,
        } => {
            panic_queries::register_assert(tcx, context, body, msg)?;
            S::Assert { condition: operand_json(context, tcx, body, cond)?, expected: *expected, message: assert_message_json(context, tcx, body, msg)?, target: target.as_u32(), unwind: unwind_json(*unwind) }
        }
        T::Yield {
            value,
            resume,
            resume_arg,
            drop,
        } => {
            S::Yield { value: operand_json(context, tcx, body, value)?, resume: resume.as_u32(), resume_arg: place_json(context, tcx, body, resume_arg)?, drop: drop.map(|bb| bb.as_u32()) }
        }
        T::CoroutineDrop => S::CoroutineDrop,
        T::FalseEdge {
            real_target,
            imaginary_target,
        } => {
            S::FalseEdge { real_target: real_target.as_u32(), imaginary_target: imaginary_target.as_u32() }
        }
        T::FalseUnwind {
            real_target,
            unwind,
        } => {
            S::FalseUnwind { real_target: real_target.as_u32(), unwind: unwind_json(*unwind) }
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
                    pool_body::AsmRegister::Register { arch: arch.map(inline_asm_arch_name), name: reg.name().into_owned() }
                }
                R::RegClass(class) => {
                    pool_body::AsmRegister::RegisterClass { arch: arch.map(inline_asm_arch_name), name: class.name().to_string() }
                }
            };
            let pieces = template.iter().map(|piece| match piece {
                P::String(text) => pool_body::AsmPiece::String { text: text.to_string() },
                P::Placeholder { operand_idx, modifier, span } => pool_body::AsmPiece::Placeholder { operand_index: *operand_idx, modifier: modifier.map(|c| c.to_string()), span: span_json(context, tcx, *span) },
            }).collect::<Vec<_>>();
            let operands = operands.iter().map(|operand| { Ok::<_, String>(match operand {
                A::In { reg, value } => pool_body::AsmOperand::In { register: register(*reg), value: operand_json(context, tcx, body, value)? },
                A::Out { reg, late, place } => pool_body::AsmOperand::Out { register: register(*reg), late: *late, place: place.as_ref().map(|p| place_json(context, tcx, body, p)).transpose()? },
                A::InOut { reg, late, in_value, out_place } => pool_body::AsmOperand::Inout { register: register(*reg), late: *late, input: operand_json(context, tcx, body, in_value)?, output: out_place.as_ref().map(|p| place_json(context, tcx, body, p)).transpose()? },
                A::Const { value } => pool_body::AsmOperand::Const { value: const_operand_json(context, tcx, body, value)? },
                A::SymFn { value } => pool_body::AsmOperand::SymFn { value: const_operand_json(context, tcx, body, value)? },
                A::SymStatic { def_id } => pool_body::AsmOperand::SymStatic { def_id: def_json(context, *def_id) },
                A::Label { target_index } => pool_body::AsmOperand::Label { target_index: *target_index },
            }) }).collect::<Result<Vec<_>, String>>()?;
            S::InlineAsm {
                asm_macro: match asm_macro { M::Asm => "asm", M::NakedAsm => "naked_asm" },
                template: pieces, operands,
                options: pool_body::AsmOptions {
                    pure: options.contains(O::PURE), nomem: options.contains(O::NOMEM), readonly: options.contains(O::READONLY),
                    preserves_flags: options.contains(O::PRESERVES_FLAGS), noreturn: options.contains(O::NORETURN), nostack: options.contains(O::NOSTACK),
                    att_syntax: options.contains(O::ATT_SYNTAX), raw: options.contains(O::RAW), may_unwind: options.contains(O::MAY_UNWIND),
                },
                line_spans: line_spans.iter().map(|span| span_json(context, tcx, *span)).collect(),
                targets: targets.iter().map(|bb| bb.as_u32()).collect(), unwind: unwind_json(*unwind),
                execution_obligation: "target-specific assembly execution is not supplied by syntax lowering",
            }
        }
    })
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

fn place_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, body: &rustc_middle::mir::Body<'tcx>, place: &rustc_middle::mir::Place<'tcx>) -> Result<pool_body::Place, String> {
    use rustc_middle::mir::ProjectionElem as P;
    use pool_body::ProjectionKind as S;
    let projection = place.iter_projections().map(|(base, elem)| {
        let projected_place = base.project_deeper(&[elem], tcx);
        let resulting_type = type_json(context, tcx, projected_place.ty(body, tcx).ty)?;
        let kind = match elem {
            P::Deref => S::Deref,
            P::Field(index, ty) => S::Field { index: index.as_u32(), field_type: type_json(context, tcx, ty)? },
            P::Index(local) => S::Index { local: local.as_u32() },
            P::ConstantIndex { offset, min_length, from_end } => S::ConstantIndex { offset, min_length, from_end },
            P::Subslice { from, to, from_end } => S::Subslice { from, to, from_end },
            P::Downcast(name, variant) => S::Downcast { name: name.map(|n| n.as_str().to_owned()), variant_index: variant.as_u32() },
            P::OpaqueCast(ty) => S::OpaqueCast { cast_type: type_json(context, tcx, ty)? },
            P::UnwrapUnsafeBinder(ty) => S::UnwrapUnsafeBinder { inner_type: type_json(context, tcx, ty)? },
            P::PhantomDeref => S::PhantomDeref,
        };
        Ok(pool_body::Projection { kind, resulting_type })
    }).collect::<Result<Vec<_>, String>>()?;
    Ok(pool_body::Place { local: place.local.as_u32(), projection, r#type: type_json(context, tcx, place.ty(body, tcx).ty)? })
}

fn operand_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &rustc_middle::mir::Operand<'tcx>,
) -> Result<pool_body::Operand, String> {
    use rustc_middle::mir::Operand as O;
    use pool_body::Operand as S;
    Ok::<_, String>(match operand {
        O::Copy(place) => {
            S::Copy { place: place_json(context, tcx, body, place)? }
        }
        O::Move(place) => {
            S::Move { place: place_json(context, tcx, body, place)? }
        }
        O::Constant(value) => {
            S::Constant { constant: const_operand_json(context, tcx, body, value)? }
        }
        O::RuntimeChecks(check) => {
            S::RuntimeChecks { check: runtime_check_json(tcx, *check) }
        }
    })
}

/// Follow `interpret/cast.rs::unsize_into` while collecting vtable demands.
/// The codegen lockstep-tail query is used by `unsize_into_ptr`, but it is not
/// a substitute for the interpreter's field traversal: wrappers such as
/// `Box<T>` contain several layers before the pointer whose pointee changes.
fn collect_unsize_vtable_demands<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    env: ty::TypingEnv<'tcx>,
    source: ty::Ty<'tcx>,
    target: ty::Ty<'tcx>,
) -> Result<(), String> {
    use rustc_middle::ty::TyKind;

    match (source.kind(), target.kind()) {
        (TyKind::Pat(source_inner, source_pattern), TyKind::Pat(target_inner, target_pattern))
            if source_pattern == target_pattern =>
        {
            return collect_unsize_vtable_demands(context, tcx, env, *source_inner, *target_inner);
        }
        (TyKind::Ref(_, source_inner, _), TyKind::Ref(_, target_inner, _))
        | (TyKind::Ref(_, source_inner, _), TyKind::RawPtr(target_inner, _))
        | (TyKind::RawPtr(source_inner, _), TyKind::RawPtr(target_inner, _)) => {
            context
                .cast_unsize_requests
                .insert((*source_inner, *target_inner));
            let (source_tail, target_tail) =
                tcx.struct_lockstep_tails_for_codegen(*source_inner, *target_inner, env);
            if let TyKind::Dynamic(target_predicates, _) = target_tail.kind() {
                match source_tail.kind() {
                    TyKind::Dynamic(source_predicates, _) => {
                        if source_predicates != target_predicates {
                            context
                                .dynamic_vtable_upcast_requests
                                .insert((source_tail, target_tail));
                            context.vtable_diagnostics.upcast_site(source_tail, target_tail);
                        }
                    }
                    _ => {
                        context
                            .vtable_query_requests
                            .insert((source_tail, target_predicates));
                        context.vtable_diagnostics.record((source_tail, target_predicates), "unsize_tail", None, None);
                    }
                }
            }
            return Ok(());
        }
        (TyKind::Adt(source_def, _), TyKind::Adt(target_def, _))
            if source_def == target_def =>
        {
            let source_layout = tcx
                .layout_of(env.as_query_input(source))
                .map_err(|error| format!("source field layout unavailable: {error:?}"))?;
            let target_layout = tcx
                .layout_of(env.as_query_input(target))
                .map_err(|error| format!("target field layout unavailable: {error:?}"))?;
            let source_count = source_layout.fields.count();
            let target_count = target_layout.fields.count();
            if source_count != target_count {
                return Err(format!(
                    "same ADT unsize has differing field counts ({source_count} vs {target_count})"
                ));
            }
            let layout_cx = ty::layout::LayoutCx::new(tcx, env);
            let mut changed = None;
            for index in 0..source_count {
                let source_field = source_layout.field(&layout_cx, index);
                let target_field = target_layout.field(&layout_cx, index);
                if source_field.is_1zst() && target_field.is_1zst() {
                    continue;
                }
                if source_field.ty == target_field.ty {
                    continue;
                }
                if changed.replace(index).is_some() {
                    return Err("unsize requires more than one changing ADT field".into());
                }
                collect_unsize_vtable_demands(
                    context,
                    tcx,
                    env,
                    source_field.ty,
                    target_field.ty,
                )?;
            }
            return Ok(());
        }
        _ => {}
    }

    // Array-to-slice and other non-vtable pointer metadata conversions do not
    // request a trait vtable. Their validity remains checked by MIR execution.
    Ok(())
}

fn vtable_allocation_for_unsize<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    source: &rustc_middle::mir::Operand<'tcx>,
    target_ty: rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<pool_body::UnsizeVtable>, String> {
    use pool_body::{UnsizeVtable as U, VtableAllocation as A, VtableQuery, VtableQueryKey, SupertraitSlotQuery};
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
        return Ok(Some(export_failure(
            "main::vtable_allocation_for_unsize",
            format!(
                "{}; {}",
                "rustc cannot provide a concrete symbolic vtable for generic or bound-variable pointee types",
                "vtable_requires_concrete_types"
            ),
        )?));
    }
    if let Err(reason) =
        collect_unsize_vtable_demands(context, tcx, body.typing_env(tcx), source_ty, target_ty)
    {
        return Ok(Some(export_failure(
            "main::vtable_allocation_for_unsize",
            format!("{}; {}", reason, "vtable_demand_collection"),
        )?));
    }
    let (source_tail, target_tail) =
        tcx.struct_lockstep_tails_for_codegen(source_pointee, target_pointee, body.typing_env(tcx));
    let ty::Dynamic(predicates, _) = target_tail.kind() else {
        return Ok(None);
    };
    Ok::<_, String>(match source_tail.kind() {
        ty::Dynamic(source_predicates, _) if source_predicates == predicates => Some(U::Allocation(A::SameDynamicVtableNoop { r#type:type_json(context,tcx,source_tail)? })),
        ty::Dynamic(..) => {
            // Miri validates the source table and then asks get_vtable_ptr for
            // the same concrete type with the destination predicate list.
            // The exact concrete candidates are closed over in
            // compiler_vtable_queries_json; this request records the runtime
            // source/destination tail pair without guessing a concrete type.
            Some(U::Allocation(A::DynamicVtableUpcast {
                source_type:type_json(context,tcx,source_ty)?, target_type:type_json(context,tcx,target_ty)?,
                source_pointee_type:type_json(context,tcx,source_pointee)?, target_pointee_type:type_json(context,tcx,target_pointee)?,
                source_tail_type:type_json(context,tcx,source_tail)?, target_tail_type:type_json(context,tcx,target_tail)?,
                supertrait_slot_query:SupertraitSlotQuery { query_kind:"supertrait_slot", typing_env:"fully_monomorphized",
                    input_source:type_json(context,tcx,source_tail)?, input_target:type_json(context,tcx,target_tail)? },
                runtime_vtable:"source_operand_metadata",
            }))
        }
        _ => {
            context
                .vtable_query_requests
                .insert((source_tail, predicates));
            context
                .vtable_diagnostics
                .record((source_tail, predicates), "unsize_cast", None, None);
            let input_type_id = context.type_id(source_tail);
            let input_predicate_ids = predicates
                .iter()
                .map(|predicate| context.predicate_id(predicate))
                .collect::<Vec<_>>();
            let input_predicates = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Result<Vec<_>, String>>()?;
            Some(U::Query(VtableQuery {
                source_type:type_json(context,tcx,source_ty)?, target_type:type_json(context,tcx,target_ty)?,
                source_pointee_type:type_json(context,tcx,source_pointee)?, target_pointee_type:type_json(context,tcx,target_pointee)?,
                input_type:type_json(context,tcx,source_tail)?, input_predicates,
                source_tail_type:type_json(context,tcx,source_tail)?, target_tail_type:type_json(context,tcx,target_tail)?,
                query_id:VtableQueryKey { input_type_id, input_predicate_ids },
            }))
        }
    })
}

fn rvalue_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    rvalue: &rustc_middle::mir::Rvalue<'tcx>,
) -> Result<pool_body::Rvalue, String> {
    use rustc_middle::mir::Rvalue as R;
    use pool_body::Rvalue as S;
    Ok::<_, String>(match rvalue {
        R::Use(value, retag) => {
            S::Use { operand: operand_json(context, tcx, body, value)?, retag: pool_body::Retag { kind: if retag.yes() { "yes" } else { "no" }, performs_retag: retag.yes() } }
        }
        R::Repeat(value, count) => {
            S::Repeat { operand: operand_json(context, tcx, body, value)?, count: const_type_json(context, tcx, *count)? }
        }
        R::Ref(region, kind, place) => {
            S::Ref { region: region_json(context, tcx, *region)?, borrow_kind: borrow_kind_json(*kind), place: place_json(context, tcx, body, place)? }
        }
        R::ThreadLocalRef(def) => {
            let initializer = if tcx.is_foreign_item(*def) {
                export_failure(
                    "main::rvalue_json",
                    "foreign thread-local initializer is unavailable",
                )?
            } else {
                match tcx.eval_static_initializer(*def) {
                    Ok(value) => pool_body::ThreadLocalInitializer { allocation: allocation_memory_payload(context, tcx, value.inner())? },
                    Err(error) => {
                        export_failure("main::rvalue_json", format!("{}", format!("{error:?}")))?
                    }
                }
            };
            S::ThreadLocalRef { global_info: static_global_info_json(tcx, *def), def_id: def_json(context, *def), def_path: tcx.def_path_str(*def), initializer }
        }
        R::RawPtr(kind, place) => {
            let pointer_kind = match kind {
                rustc_middle::mir::RawPtrKind::Mut => pool_body::RawPointerKind::Mutable,
                rustc_middle::mir::RawPtrKind::Const => pool_body::RawPointerKind::Constant,
                rustc_middle::mir::RawPtrKind::FakeForPtrMetadata => pool_body::RawPointerKind::MetadataOnly,
            };
            S::RawPtr { pointer_kind, place: place_json(context, tcx, body, place)? }
        }
        R::Cast(kind, value, target) => {
            if matches!(
                kind,
                rustc_middle::mir::CastKind::PointerCoercion(
                    ty::adjustment::PointerCoercion::ReifyFnPointer(_)
                        | ty::adjustment::PointerCoercion::ClosureFnPointer(_),
                    _
                )
            ) {
                context.fn_pointer_cast_inputs.insert(value.ty(body, tcx));
            }
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
                vtable_allocation_for_unsize(context, tcx, body, value, *target)?
            } else {
                None
            };
            let (vtable_allocation, vtable_query) = match vtable {
                Some(pool_body::UnsizeVtable::Allocation(allocation)) => (Some(allocation), None),
                Some(pool_body::UnsizeVtable::Query(query)) => (None, Some(query)),
                None => (None, None),
            };
            S::Cast { cast_kind: cast_kind_json(*kind), operand: operand_json(context, tcx, body, value)?,
                target_type: type_json(context, tcx, *target)?, vtable_allocation, vtable_query, vtable_probe: None }
        }
        R::BinaryOp(op, pair) => {
            // rustc's `ImmTy::from_pair` performs a real `layout_of` query for
            // `(overflow-value-type, bool)` whenever an overflow operation
            // materializes its scalar pair. `Offset` reaches that same helper
            // internally with the RHS type as its value type. Preserve this
            // implicit source-operation query in the runtime type-demand
            // closure; it is not enough that the operands themselves appear
            // in MIR, since rustc constructs the tuple only inside the helper.
            let overflow_value_ty = match op {
                rustc_middle::mir::BinOp::AddWithOverflow
                | rustc_middle::mir::BinOp::SubWithOverflow
                | rustc_middle::mir::BinOp::MulWithOverflow => Some(pair.0.ty(body, tcx)),
                rustc_middle::mir::BinOp::Offset => Some(pair.1.ty(body, tcx)),
                _ => None,
            };
            let implicit_overflow_tuple_type = overflow_value_ty
                .map(|value_ty| {
                    {
                        type_json(
                            context,
                            tcx,
                            ty::Ty::new_tup(tcx, &[value_ty, tcx.types.bool]),
                        )
                    }
                })
                .transpose()?;
            S::BinaryOp { operator: pool_body::Operator { kind: binop_name(*op) }, left: operand_json(context, tcx, body, &pair.0)?, right: operand_json(context, tcx, body, &pair.1)?, implicit_overflow_tuple_type }
        }
        R::UnaryOp(op, value) => {
            S::UnaryOp { operator: pool_body::Operator { kind: unop_name(*op) }, operand: operand_json(context, tcx, body, value)? }
        }
        R::Discriminant(place) => {
            S::Discriminant { place: place_json(context, tcx, body, place)? }
        }
        R::Aggregate(kind, values) => {
            S::Aggregate { aggregate_kind: aggregate_kind_json(context, tcx, kind)?, operands: values.iter().map(|value| operand_json(context, tcx, body, value)).collect::<Result<Vec<_>, String>>()? }
        }
        R::CopyForDeref(place) => {
            S::CopyForDeref { place: place_json(context, tcx, body, place)? }
        }
        R::WrapUnsafeBinder(value, ty) => {
            S::WrapUnsafeBinder { operand: operand_json(context, tcx, body, value)?, r#type: type_json(context, tcx, *ty)? }
        }
        R::Reborrow(ty, mutability, place) => {
            S::Reborrow { r#type: type_json(context, tcx, *ty)?, mutability: mutability_json(*mutability), place: place_json(context, tcx, body, place)? }
        }
    })
}

fn borrow_kind_json(kind: rustc_middle::mir::BorrowKind) -> pool_body::BorrowKind {
    use rustc_middle::mir::BorrowKind as B;
    use pool_body::BorrowKind as S;
    match kind {
        B::Shared => S::Shared,
        B::Fake(fake) => {
            let fake_kind = match fake {
                rustc_middle::mir::FakeBorrowKind::Shallow => "shallow",
                rustc_middle::mir::FakeBorrowKind::Deep => "deep",
            };
            S::Fake { fake_kind, retag_mode: "default" }
        }
        B::Mut { kind } => {
            let mut_kind = match kind {
                rustc_middle::mir::MutBorrowKind::Default => "default",
                rustc_middle::mir::MutBorrowKind::TwoPhaseBorrow => "two_phase",
                rustc_middle::mir::MutBorrowKind::ClosureCapture => "closure_capture",
            };
            S::Mutable { mutability_kind: mut_kind }
        }
    }
}

fn safety_json(safety: rustc_hir::Safety) -> pool_type::Safety {
    match safety {
        rustc_hir::Safety::Safe => pool_type::Safety::Safe,
        rustc_hir::Safety::Unsafe => pool_type::Safety::Unsafe,
    }
}

fn mutability_json(mutability: rustc_ast::Mutability) -> pool_type::Mutability {
    match mutability {
        rustc_ast::Mutability::Mut => pool_type::Mutability::Mutable,
        rustc_ast::Mutability::Not => pool_type::Mutability::Immutable,
    }
}

fn extern_abi_json(abi: rustc_abi::ExternAbi) -> pool_type::ExternAbi {
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
    pool_type::ExternAbi {
        kind,
        unwind,
    }
}

fn unwind_terminate_reason_json(reason: rustc_middle::mir::UnwindTerminateReason) -> pool_body::UnwindTerminateReason {
    use rustc_middle::mir::UnwindTerminateReason as R;
    match reason { R::Abi => pool_body::UnwindTerminateReason::Abi,
        R::InCleanup => pool_body::UnwindTerminateReason::InCleanup }
}

fn cast_kind_json(kind: rustc_middle::mir::CastKind) -> pool_body::CastKind {
    use rustc_middle::mir::CastKind as C;
    use pool_body::{CastKind as S, PointerCoercion as Q};
    use rustc_middle::ty::adjustment::PointerCoercion as P;
    match kind {
        C::PointerExposeProvenance => {
            S::PointerExposeProvenance
        }
        C::PointerWithExposedProvenance => {
            S::PointerWithExposedProvenance
        }
        C::PointerCoercion(coercion, source) => {
            let coercion = match coercion {
                P::ReifyFnPointer(safety) => {
                    Q::ReifyFnPointer { safety: safety_json(safety) }
                }
                P::UnsafeFnPointer => Q::UnsafeFnPointer,
                P::ClosureFnPointer(safety) => {
                    Q::ClosureFnPointer { safety: safety_json(safety) }
                }
                P::MutToConstPointer => Q::MutToConstPointer,
                P::ArrayToPointer => Q::ArrayToPointer,
                P::Unsize => Q::Unsize,
            };
            let source = match source {
                rustc_middle::mir::CoercionSource::AsCast => pool_body::CoercionSource::AsCast,
                rustc_middle::mir::CoercionSource::Implicit => pool_body::CoercionSource::Implicit,
            };
            S::PointerCoercion { coercion, source }
        }
        C::IntToInt => S::IntToInt,
        C::FloatToInt => S::FloatToInt,
        C::FloatToFloat => S::FloatToFloat,
        C::IntToFloat => S::IntToFloat,
        C::PtrToPtr => S::PtrToPtr,
        C::FnPtrToPtr => S::FnPtrToPtr,
        C::Transmute => S::Transmute,
        C::BoxDerefTransmute => S::BoxDerefTransmute,
        C::Subtype => S::Subtype,
    }
}

fn aggregate_kind_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    kind: &rustc_middle::mir::AggregateKind<'tcx>,
) -> Result<pool_body::AggregateKind, String> {
    use rustc_middle::mir::AggregateKind as A;
    use pool_body::AggregateKind as S;
    Ok::<_, String>(match kind {
        A::Array(ty) => S::Array { element_type: type_json(context, tcx, *ty)? },
        A::Tuple => S::Tuple,
        A::Adt(def, variant, args, user_ty, active_field) => {
            S::Adt { def_id: def_json(context, *def), def_path: tcx.def_path_str(*def), variant_index: variant.as_u32(), generic_args: generic_args_json(context, tcx, *args)?, user_type_annotation: user_ty.map(|value| pool_constant::Annotation::AnnotationRef { index: value.as_u32() }), active_union_field: active_field.map(|field| field.as_u32()) }
        }
        A::Closure(def, args) => {
            S::Closure { def_id: def_json(context, *def), def_path: tcx.def_path_str(*def), generic_args: generic_args_json(context, tcx, *args)? }
        }
        A::Coroutine(def, args) => {
            S::Coroutine { def_id: def_json(context, *def), def_path: tcx.def_path_str(*def), generic_args: generic_args_json(context, tcx, *args)? }
        }
        A::CoroutineClosure(def, args) => {
            S::CoroutineClosure { def_id: def_json(context, *def), def_path: tcx.def_path_str(*def), generic_args: generic_args_json(context, tcx, *args)? }
        }
        A::RawPtr(ty, mutability) => {
            S::RawPtr { pointee_type: type_json(context, tcx, *ty)?, mutability: mutability_json(*mutability) }
        }
    })
}

fn assert_message_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    message: &rustc_middle::mir::AssertMessage<'tcx>,
) -> Result<pool_body::AssertMessage, String> {
    use rustc_middle::mir::AssertKind as A;
    use pool_body::AssertMessage as S;
    Ok::<_, String>(match message {
        A::BoundsCheck { len, index } => {
            S::BoundsCheck { length: operand_json(context, tcx, body, len)?, index: operand_json(context, tcx, body, index)? }
        }
        A::Overflow(op, left, right) => {
            S::Overflow { operator: pool_body::Operator { kind: binop_name(*op) }, left: operand_json(context, tcx, body, left)?, right: operand_json(context, tcx, body, right)? }
        }
        A::OverflowNeg(value) => {
            S::OverflowNeg { operand: operand_json(context, tcx, body, value)? }
        }
        A::DivisionByZero(value) => {
            S::DivisionByZero { operand: operand_json(context, tcx, body, value)? }
        }
        A::RemainderByZero(value) => {
            S::RemainderByZero { operand: operand_json(context, tcx, body, value)? }
        }
        A::ResumedAfterReturn(kind) => {
            S::ResumedAfterReturn { coroutine_kind: coroutine_kind_json(*kind) }
        }
        A::ResumedAfterPanic(kind) => {
            S::ResumedAfterPanic { coroutine_kind: coroutine_kind_json(*kind) }
        }
        A::ResumedAfterDrop(kind) => {
            S::ResumedAfterDrop { coroutine_kind: coroutine_kind_json(*kind) }
        }
        A::MisalignedPointerDereference { required, found } => {
            S::MisalignedPointerDereference { required: operand_json(context, tcx, body, required)?, found: operand_json(context, tcx, body, found)? }
        }
        A::NullPointerDereference => S::NullPointerDereference,
        A::NullReferenceConstructed => S::NullReferenceConstructed,
        A::InvalidEnumConstruction(value) => {
            S::InvalidEnumConstruction { operand: operand_json(context, tcx, body, value)? }
        }
    })
}

fn unwind_json(unwind: rustc_middle::mir::UnwindAction) -> pool_body::Unwind {
    use rustc_middle::mir::UnwindAction as U;
    use pool_body::Unwind as S;
    match unwind {
        U::Continue => S::Continue,
        U::Unreachable => S::Unreachable,
        U::Terminate(reason) => S::Terminate { reason: unwind_terminate_reason_json(reason) },
        U::Cleanup(block) => S::Cleanup { target: block.as_u32() },
    }
}

fn def_json(context: &mut ExportContext<'_>, def: rustc_hir::def_id::DefId) -> u64 {
    let (id,fresh)=context.definitions.reserve(def);
    if fresh { context.definitions.define(id,pool_values::Definition { crate_index:def.krate.as_u32(),index:def.index.as_u32() }); }
    id as u64
}

fn register_call_transfer_covariance<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    caller_body: &rustc_middle::mir::Body<'tcx>,
    func_ty: ty::Ty<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
    instance: ty::Instance<'tcx>,
    return_destination: ty::Ty<'tcx>,
) -> Result<(), String> {
    Ok::<_, String>({
        let Some(mut request) = call_transfer_request(
            tcx,
            caller_body,
            func_ty,
            call_args,
            Some(instance),
            return_destination,
        )?
        else {
            return Ok(());
        };
        request.caller_instance = Some(instance);
        if matches!(instance.def, ty::InstanceKind::Virtual(..)) {
            context.virtual_call_transfers.push((instance, request));
            return Ok(());
        }
        register_call_transfer_for_target(context, tcx, &request, instance, None, false)?;
    })
}

fn call_transfer_request<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_body: &rustc_middle::mir::Body<'tcx>,
    func_ty: ty::Ty<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
    caller_instance: Option<ty::Instance<'tcx>>,
    return_destination: ty::Ty<'tcx>,
) -> Result<Option<CallTransferRequest<'tcx>>, String> {
    let env = caller_body.typing_env(tcx);
    let signature = tcx
        .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(func_ty.fn_sig(tcx)))
        .map_err(|error| format!("call transfer signature normalization failed: {error:?}"))?;
    let signature = tcx.instantiate_bound_regions_with_erased(signature);
    let mut caller_arg_types = call_args
        .iter()
        .map(|arg| arg.node.ty(caller_body, tcx))
        .collect::<Vec<_>>();
    // This is the same untupling done by init_fn_call before it calls
    // init_stack_frame. Its final operand must be a tuple; if malformed, the
    // source interpreter itself stops before argument copying.
    if signature.abi() == rustc_abi::ExternAbi::RustCall && !caller_arg_types.is_empty() {
        let tuple = caller_arg_types.pop().unwrap();
        let ty::Tuple(fields) = tuple.kind() else {
            return Ok(None);
        };
        caller_arg_types.extend(fields.iter());
    }
    let extra_types = if let Some(extra) = call_args.get(signature.inputs().len()..) {
        tcx.mk_type_list_from_iter(extra.iter().map(|arg| arg.node.ty(caller_body, tcx)))
    } else {
        ty::List::empty()
    };
    Ok(Some(CallTransferRequest {
        function_ty: func_ty,
        caller_env: env,
        caller_instance,
        caller_args: caller_arg_types,
        extra_types,
        return_destination,
        generated_caller_abi: None,
    }))
}

fn register_call_transfer_for_target<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    request: &CallTransferRequest<'tcx>,
    instance: ty::Instance<'tcx>,
    virtual_receiver: Option<ty::Ty<'tcx>>,
    indirect_function_pointer: bool,
) -> Result<(), String> {
    if matches!(instance.def, ty::InstanceKind::Item(_)) && tcx.is_foreign_item(instance.def_id()) {
        let key = (instance, request.clone(), indirect_function_pointer);
        if context.foreign_call_transfer_keys.insert(key) {
            context.foreign_call_transfers.push((instance, request.clone(), indirect_function_pointer));
        }
        return Ok(());
    }
    if !closed_covariance_ty(request.function_ty)
        || !closed_covariance_ty(request.return_destination)
        || request
            .caller_args
            .iter()
            .any(|ty| !closed_covariance_ty(*ty))
        || instance.args.has_non_region_param()
        || instance.args.has_escaping_bound_vars()
        || instance.args.has_infer()
        || instance.args.has_placeholders()
        || instance.args.references_error()
        || request.extra_types.has_non_region_param()
        || request.extra_types.has_escaping_bound_vars()
        || request.extra_types.has_infer()
        || request.extra_types.has_placeholders()
        || request.extra_types.references_error()
    {
        return Ok(());
    }
    let def_id = instance.def.def_id();
    match instance.def {
        ty::InstanceKind::Intrinsic(..)
        | ty::InstanceKind::LlvmIntrinsic(..)
        | ty::InstanceKind::Virtual(..) => return Ok(()),
        ty::InstanceKind::Item(_)
            if tcx.is_foreign_item(def_id)
                || !has_instance_mir_source(tcx, def_id)
                || is_required_trait_method(tcx, def_id) =>
        {
            return Ok(());
        }
        _ => {}
    }
    let Some(callee_abi) =
        instance_fn_abi_with_extras(tcx, request.caller_env, instance, request.extra_types)?
    else {
        return Ok(());
    };
    let caller_location = if request.generated_caller_abi.is_some() {
        instance.def.requires_caller_location(tcx)
    } else {
        request
            .caller_instance
            .is_some_and(|caller| caller.def.requires_caller_location(tcx))
    };
    let generated_caller_ty = if let Some(caller_abi) = request.generated_caller_abi {
        let inputs = request
            .caller_args
            .iter()
            .copied()
            .chain(caller_location.then(|| tcx.caller_location_ty()));
        let signature = tcx.mk_fn_sig(
            inputs,
            request.return_destination,
            ty::FnSigKind::default()
                .set_abi(caller_abi)
                .set_safety(rustc_hir::Safety::Safe),
        );
        let caller_ty = ty::Ty::new_fn_ptr(tcx, ty::Binder::dummy(signature));
        let _ = type_json(context, tcx, caller_ty)?;
        caller_ty
    } else {
        request.function_ty
    };
    let caller_abi = if let Some(caller_instance) = request.caller_instance {
        instance_fn_abi_with_extras(
            tcx,
            request.caller_env,
            caller_instance,
            request.extra_types,
        )?
    } else {
        fn_ptr_abi_with_extras(
            tcx,
            request.caller_env,
            generated_caller_ty.fn_sig(tcx),
            request.extra_types,
        )?
    };
    let Some(caller_abi) = caller_abi else {
        return Ok(());
    };
    let mut caller_abi = caller_abi.clone();
    if let Some(receiver_ty) = virtual_receiver {
        if let Some(receiver) = caller_abi.args.first_mut() {
            // Miri's Virtual branch patches this type after resolving the
            // runtime vtable slot; the ABI layout itself remains unchanged.
            receiver.layout.ty = receiver_ty;
        } else {
            return Ok(());
        }
    }

    let closure_receiver = (matches!(
        instance.def,
        ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { .. })
    ) || tcx.is_closure_like(instance.def_id()))
        && callee_abi.args.first().is_some_and(|arg| {
            matches!(arg.layout.ty.kind(), ty::Closure(_, args)
                if args.as_closure().upvar_tys().is_empty())
        });
    if indirect_function_pointer && instance.def.requires_caller_location(tcx) {
        // FnPtr dispatch passes with_caller_location=false in pinned step.rs.
        return Ok(());
    }
    if let Some(caller_instance) = request.caller_instance {
        if caller_instance.def.requires_caller_location(tcx)
            != instance.def.requires_caller_location(tcx)
        {
            return Ok(());
        }
    }

    if caller_location != instance.def.requires_caller_location(tcx) {
        return Ok(());
    }

    // Use the same substituted body that the source interpreter enters. ABI
    // argument types are validation metadata; the actual copy destination is
    // the instantiated MIR local (or spread tuple field).
    let template = tcx.instance_mir(instance.def);
    let callee_body = match instance.try_instantiate_mir_and_normalize_erasing_regions(
        tcx,
        template.typing_env(tcx),
        ty::EarlyBinder::bind(tcx, template.clone()),
    ) {
        Ok(body) => body,
        Err(error) => return Err(format!("callee MIR instantiation failed: {error:?}")),
    };
    let caller_args = if caller_location {
        caller_abi
            .args
            .get(..caller_abi.args.len().saturating_sub(1))
    } else {
        Some(&caller_abi.args[..])
    };
    let callee_args = if caller_location {
        callee_abi
            .args
            .get(..callee_abi.args.len().saturating_sub(1))
    } else {
        Some(&callee_abi.args[..])
    };
    let (Some(caller_args_abi), Some(callee_args_abi)) = (caller_args, callee_args) else {
        return Ok(());
    };

    if caller_abi.conv != callee_abi.conv
        || caller_abi.c_variadic != callee_abi.c_variadic
        || (caller_abi.c_variadic && caller_abi.fixed_count != callee_abi.fixed_count)
    {
        return Ok(());
    }

    let mut source_types = request.caller_args.clone();
    if let Some(receiver_ty) = virtual_receiver {
        if let Some(receiver) = source_types.first_mut() {
            *receiver = receiver_ty;
        } else {
            return Ok(());
        }
    }

    // Miri's non-capturing-closure rule may initialize the first callee
    // local without copying it. It consumes a caller operand only when both
    // complete ABI argument lists have the same length.
    let caller_has_closure_receiver =
        closure_receiver && caller_abi.args.len() == callee_abi.args.len();
    let mut target_local_types = Vec::new();
    for local in callee_body.args_iter() {
        let local_ty = callee_body.local_decls[local].ty;
        if closure_receiver && local == rustc_middle::mir::Local::arg(0) {
            continue;
        }
        if callee_abi.c_variadic
            && local == rustc_middle::mir::Local::from_usize(callee_body.arg_count)
        {
            // Miri packages extras into this synthetic VaList. They are
            // checked/initialized by allocate_varargs, not copied into this
            // local through copy_op_allow_transmute.
            break;
        }
        if Some(local) == callee_body.spread_arg {
            let ty::Tuple(fields) = local_ty.kind() else {
                return Ok(());
            };
            for field_ty in fields.iter() {
                target_local_types.push(field_ty);
            }
        } else {
            target_local_types.push(local_ty);
        }
    }

    let fixed_count = if callee_abi.c_variadic {
        usize::try_from(callee_abi.fixed_count).unwrap_or(usize::MAX)
    } else {
        target_local_types.len()
    };
    let transfer_count = fixed_count
        .min(target_local_types.len())
        .min(
            source_types
                .len()
                .saturating_sub(usize::from(caller_has_closure_receiver)),
        )
        .min(caller_args_abi.len())
        .min(callee_args_abi.len());
    for index in 0..transfer_count {
        let source_index = index + usize::from(caller_has_closure_receiver);
        let Some(source) = source_types.get(source_index).copied() else {
            break;
        };
        let Some(caller_arg_abi) = caller_args_abi.get(source_index) else {
            break;
        };
        let Some(callee_arg_abi) = callee_args_abi.get(index + usize::from(closure_receiver))
        else {
            break;
        };
        // `eq_abi` is a necessary source check before argument copying. The
        // exact covariance result still comes only from rustc; candidates
        // rejected by Miri's additional type-based layout check can therefore
        // add harmless facts but cannot change call selection or acceptance.
        if !caller_arg_abi.eq_abi(callee_arg_abi) {
            break;
        }
        record_covariance_transfer(context, source, target_local_types[index]);
    }

    // The source transfers the callee return local to the caller destination
    // after the body returns. FnAbi validates the transfer; covariance uses
    // the instantiated MIR return-place type.
    Ok::<_, String>(if caller_abi.ret.eq_abi(&callee_abi.ret) {
        record_covariance_transfer(
            context,
            callee_body.local_decls[rustc_middle::mir::RETURN_PLACE].ty,
            request.return_destination,
        );
    })
}

/// `FnAbiDesc::for_instance` in pinned rustc asserts that extra arguments are
/// empty for RustCall and for every non-C-variadic signature. Querying the
/// empty-extra ABI first is valid for every callable instance and gives the
/// compiler-authored variadic bit. Only then may the source-provided extras be
/// passed to rustc's ABI query. This is a metadata-capture guard: it does not
/// select or reject runtime call targets.
fn instance_fn_abi_with_extras<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: ty::TypingEnv<'tcx>,
    instance: ty::Instance<'tcx>,
    extra_types: &'tcx ty::List<ty::Ty<'tcx>>,
) -> Result<Option<&'tcx rustc_target::callconv::FnAbi<'tcx, ty::Ty<'tcx>>>, String> {
    let empty = ty::List::empty();
    let baseline = tcx
        .fn_abi_of_instance(env.as_query_input((instance, empty)))
        .map_err(|error| format!("baseline ABI query failed: {error:?}"))?;
    if extra_types.is_empty() {
        return Ok(Some(baseline));
    }
    if !baseline.c_variadic {
        return Ok(None);
    }
    tcx.fn_abi_of_instance(env.as_query_input((instance, extra_types)))
        .map(Some)
        .map_err(|error| format!("variadic ABI query failed: {error:?}"))
}

/// The function-pointer query has the same pinned ABI precondition as the
/// instance query. Consult its empty-extra compiler ABI before asking about
/// any variadic operands.
fn fn_ptr_abi_with_extras<'tcx>(
    tcx: TyCtxt<'tcx>,
    env: ty::TypingEnv<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    extra_types: &'tcx ty::List<ty::Ty<'tcx>>,
) -> Result<Option<&'tcx rustc_target::callconv::FnAbi<'tcx, ty::Ty<'tcx>>>, String> {
    let empty = ty::List::empty();
    let baseline = tcx
        .fn_abi_of_fn_ptr(env.as_query_input((signature, empty)))
        .map_err(|error| format!("baseline ABI query failed: {error:?}"))?;
    if extra_types.is_empty() {
        return Ok(Some(baseline));
    }
    if !baseline.c_variadic {
        return Ok(None);
    }
    tcx.fn_abi_of_fn_ptr(env.as_query_input((signature, extra_types)))
        .map(Some)
        .map_err(|error| format!("variadic ABI query failed: {error:?}"))
}

fn record_covariance_transfer<'tcx>(
    context: &mut ExportContext<'tcx>,
    source: ty::Ty<'tcx>,
    target: ty::Ty<'tcx>,
) {
    if source != target && closed_covariance_ty(source) && closed_covariance_ty(target) {
        context.covariance_query_requests.insert((source, target));
        context.runtime_type_query_demands.insert(source);
        context.runtime_type_query_demands.insert(target);
    }
}

/// backtrace.rs builds a function pointer directly from each active frame's
/// Instance. These requests are absent from MIR ReifyFnPointer casts, so the
/// prepared AllocId profile must reserve the same compiler keys explicitly.
/// Restrict this closure to compilations whose emitted MIR calls a Miri API
/// that constructs those pointers; otherwise programs pay no extra key probes.
fn register_backtrace_frame_pointer_demands<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) {
    if !context.backtrace_demanded {
        context.backtrace_demanded = context.instance_events[context.backtrace_event_cursor..]
            .iter().any(|instance| {
                matches!(instance.def, ty::InstanceKind::Item(_))
                    && tcx.is_foreign_item(instance.def_id())
                    && matches!(tcx.symbol_name(*instance).name,
                        "miri_get_backtrace" | "miri_resolve_frame")
            });
    }
    context.backtrace_event_cursor = context.instance_events.len();
    if context.backtrace_demanded {
        // Only emitted MIR frames are eligible; append each new frame once.
        context.fn_pointer_targets.extend(
            context.runtime_mir_frame_instances.suffix(context.backtrace_frame_cursor).iter().copied());
        context.backtrace_frame_cursor = context.runtime_mir_frame_instances.len();
    }
}

/// The winner comes from foreign_symbols' exact weak/duplicate/non-function
/// selection, not an ABI-compatible candidate search. Reuse ordinary call
/// transfer discovery; each answer is still evaluated by rustc's Covariant
/// relation, including false answers used by copy_op_allow_transmute.
fn register_selected_foreign_call_transfers<'tcx>(
    context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, symbol: &str,
    target: ty::Instance<'tcx>,
) -> Result<(), String> {
    for site in 0..context.foreign_call_transfers.len() {
        let (declaration, request, indirect) = context.foreign_call_transfers[site].clone();
        if tcx.symbol_name(declaration).name != symbol ||
            !context.processed_foreign_transfers.insert((site, target)) {
            continue;
        }
        register_call_transfer_for_target(context, tcx, &request, target, None, indirect)?;
    }
    Ok(())
}

fn register_fn_pointer_call_transfers<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<(), String> {
    let targets = context.fn_pointer_targets.len();
    let sites = context.fn_pointer_call_transfers.len();
    let frontier = context.processed_fn_pointer_transfers;
    for call_site in frontier.site_start(targets)..sites {
            let request = context.fn_pointer_call_transfers[call_site].clone();
            for target_index in frontier.target_start(call_site)..targets {
                let target = *context.fn_pointer_targets.get_index(target_index).unwrap();
                if matches!(target.def, ty::InstanceKind::Item(_))
                    && tcx.is_foreign_item(target.def_id())
                    && fn_pointer_call_abi_matches_candidate(tcx, &request, target)?
                {
                    register_runtime_callback_call_types(
                        context,
                        tcx,
                        tcx.symbol_name(target).name.to_string(),
                        &request.caller_args,
                    )?;
                }
                register_call_transfer_for_target(context, tcx, &request, target, None, true)?;
            }
        }
    context.processed_fn_pointer_transfers.complete(sites, targets);
    Ok(())
}

/// A function-pointer candidate can contribute a runtime-generated callback
/// signature only when its compiler ABI can serve this callsite. This keeps
/// unrelated foreign candidates from promoting callback operand types into
/// the runtime query set. `eq_abi` deliberately checks ABI compatibility
/// rather than requiring source and target Ty identity.
fn fn_pointer_call_abi_matches_candidate<'tcx>(
    tcx: TyCtxt<'tcx>,
    request: &CallTransferRequest<'tcx>,
    candidate: ty::Instance<'tcx>,
) -> Result<bool, String> {
    Ok({
        let Some(callsite_abi) = fn_ptr_abi_with_extras(
            tcx,
            request.caller_env,
            request.function_ty.fn_sig(tcx),
            request.extra_types,
        )?
        else {
            return Ok(false);
        };
        let Some(candidate_abi) =
            instance_fn_abi_with_extras(tcx, request.caller_env, candidate, request.extra_types)?
        else {
            return Ok(false);
        };

        callsite_abi.conv == candidate_abi.conv
            && callsite_abi.c_variadic == candidate_abi.c_variadic
            && callsite_abi.fixed_count == candidate_abi.fixed_count
            && callsite_abi.args.len() == candidate_abi.args.len()
            && callsite_abi
                .args
                .iter()
                .zip(candidate_abi.args.iter())
                .all(|(call_arg, candidate_arg)| call_arg.eq_abi(candidate_arg))
            && callsite_abi.ret.eq_abi(&candidate_abi.ret)
    })
}

/// Capture the function-pointer call which Miri constructs for the required
/// POSIX callback registrations. These are not guest MIR call terminators:
/// helpers.rs::call_function builds a fresh C caller signature from the
/// runtime argument and destination layouts, then adds caller_location when
/// the selected instance requires it.
fn register_runtime_callback_call<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    instance: ty::Instance<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
) -> Result<(), String> {
    Ok::<_, String>({
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !tcx.is_foreign_item(instance.def.def_id())
        {
            return Ok(());
        }
        let source_symbol = tcx.symbol_name(instance).name.to_string();
        let call_arg_types = call_args
            .iter()
            .map(|arg| arg.node.ty(body, tcx))
            .collect::<Vec<_>>();
        register_runtime_callback_call_types(context, tcx, source_symbol, &call_arg_types)?;
    })
}

/// Match the target checks in the pinned Unix and Windows Miri
/// `_Unwind_RaiseException` handlers. These are the only targets where Miri
/// forwards this foreign shim's payload into its unwind state.
fn miri_handles_unwind_raise_exception(tcx: TyCtxt<'_>) -> bool {
    matches!(
        tcx.sess.target.os,
        rustc_target::spec::Os::Linux
            | rustc_target::spec::Os::FreeBsd
            | rustc_target::spec::Os::Illumos
            | rustc_target::spec::Os::Solaris
            | rustc_target::spec::Os::Android
            | rustc_target::spec::Os::MacOs
    ) || (tcx.sess.target.os == rustc_target::spec::Os::Windows
        && tcx.sess.target.env == rustc_target::spec::Env::Gnu)
}

/// Shared by direct FnDef calls and indirect FnPtr calls whose exact compiler
/// candidate is a foreign item. The candidate symbol comes from rustc's
/// resolved function allocation/cast identity; `call_arg_types` come from the
/// actual callsite operand types.
fn register_runtime_callback_call_types<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    source_symbol: String,
    call_arg_types: &[ty::Ty<'tcx>],
) -> Result<(), String> {
    Ok::<_, String>({
        if source_symbol == "miri_start_unwind" {
            // `shims/foreign_items.rs::miri_start_unwind` checks its argument as
            // `*mut ()`. check_shim_sig transmutates the caller operand to that
            // expected layout before Miri stores it in the unwind state, so the
            // callback signature uses the descriptor's post-check type.
            if call_arg_types.len() == 1 {
                let payload = shim_abi::descriptor(tcx, "unitPointer")?;
                generated_call_queries::register_unwind_payload_type(context, payload);
            }
            return Ok(());
        }
        if source_symbol == "_Unwind_RaiseException" {
            if miri_handles_unwind_raise_exception(tcx) && call_arg_types.len() == 1 {
                // The Unix/Windows-GNU handler checks this C shim with wildcard
                // `* _`, which check_shim_sig resolves to the machine's canonical
                // void pointer and transmutes before forwarding to the Rust shim.
                // Register that checked type, not the raw MIR operand (often
                // `*mut u8`), so the generated callback ABI matches Miri's state.
                let payload = shim_abi::descriptor(tcx, "pointer")?;
                generated_call_queries::register_unwind_payload_type(context, payload);
            }
            return Ok(());
        }
        if source_symbol == "__cxa_thread_atexit_impl"
            && tcx.sess.target.env != rustc_target::spec::Env::Gnu
        {
            return Ok(());
        }
        let unit_ptr_mut = ty::Ty::new_mut_ptr(tcx, tcx.types.unit);
        let (callback_index, caller_args, return_destination, caller_abi) =
            match source_symbol.as_str() {
                // shims/unix/thread.rs::pthread_create calls the registered routine
                // with the MIR-typed `arg` operand and a `*mut ()` return place.
                "pthread_create" if call_arg_types.len() >= 4 => (
                    2,
                    vec![call_arg_types[3]],
                    unit_ptr_mut,
                    rustc_abi::ExternAbi::C { unwind: false },
                ),
                // pthread TLS destructors and Linux __cxa_thread_atexit_impl both
                // schedule callbacks with unit_ptr_mut and no return place; helpers.rs
                // substitutes a fake unit ZST destination in that case.
                "pthread_key_create" if call_arg_types.len() >= 2 => (
                    1,
                    vec![unit_ptr_mut],
                    tcx.types.unit,
                    rustc_abi::ExternAbi::C { unwind: false },
                ),
                "__cxa_thread_atexit_impl" if call_arg_types.len() >= 3 => (
                    0,
                    vec![unit_ptr_mut],
                    tcx.types.unit,
                    rustc_abi::ExternAbi::C { unwind: false },
                ),
                // foreign_items.rs::miri_thread_spawn calls start_regular_thread with
                // Rust ABI, one checked *mut () data argument, and machine.layouts.unit.
                "miri_thread_spawn" if call_arg_types.len() >= 2 => (
                    0,
                    vec![unit_ptr_mut],
                    tcx.types.unit,
                    rustc_abi::ExternAbi::Rust,
                ),
                "miri_thread_join" | "miri_run_provenance_gc" => return Ok(()),
                _ => return Ok(()),
            };
        let Some(callback_operand_type) = call_arg_types.get(callback_index).copied() else {
            return Ok(());
        };
        generated_call_queries::register_runtime_callback_call_types(
            context,
            tcx,
            source_symbol,
            callback_operand_type,
            caller_args,
            return_destination,
            caller_abi,
        )?;
    })
}

fn register_catch_unwind_intrinsic<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
) -> Result<(), String> {
    let ty::InstanceKind::Intrinsic(def) = instance.def else {
        return Ok(());
    };
    let Some(intrinsic) = tcx.intrinsic(def) else {
        return Ok(());
    };
    Ok::<_, String>(if intrinsic.name.as_str() == "catch_unwind" {
        generated_call_queries::register_catch_unwind_site(context, tcx, body, call_args)?;
    })
}

fn register_runtime_callback_transfers<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Result<(), String> {
    generated_call_queries::register_catch_unwind_transfers(context, tcx)?;
    let targets = context.fn_pointer_targets.len();
    let sites = context.runtime_callback_transfers.len();
    let frontier = context.processed_runtime_callback_transfers;
    for call_site in frontier.site_start(targets)..sites {
            let callback = context.runtime_callback_transfers[call_site].clone();
            // Keep the registration operand type attached to the request as
            // provenance. It intentionally is not an exact type-equality filter:
            // function-pointer casts and the runtime's *mut ()/c_void ABI contract
            // can differ in Ty while still reaching this generated call path.
            let _registration_operand_type = callback.callback_operand_type;
            let _registration_symbol = callback.source_symbol;
            for target_index in frontier.target_start(call_site)..targets {
                let target = *context.fn_pointer_targets.get_index(target_index).unwrap();
                // Generic VTable shim projections are not concrete callback
                // bodies; querying their FnAbi can ICE on an escaping projection.
                // They remain in the exact candidate catalog and source dispatch
                // remains unchanged, but cannot provide a substituted MIR local
                // transfer here.
                if matches!(target.def, ty::InstanceKind::Shim(ty::ShimKind::VTable(_))) {
                    continue;
                }
                register_call_transfer_for_target(
                    context,
                    tcx,
                    &callback.request,
                    target,
                    None,
                    false,
                )?;
            }
        }
    context.processed_runtime_callback_transfers.complete(sites, targets);
    Ok(())
}

fn register_virtual_call_transfers<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    virtual_instance: ty::Instance<'tcx>,
    concrete_self: ty::Ty<'tcx>,
    concrete_target: ty::Instance<'tcx>,
    call_site: usize,
) -> Result<(), String> {
    let receiver = ty::Ty::new_mut_ptr(tcx, concrete_self);

        let (recorded_instance, request) = context.virtual_call_transfers[call_site].clone();
        if recorded_instance != virtual_instance
            || !context
                .processed_virtual_transfers
                .insert((call_site, concrete_target))
        {
            return Ok(());
        }
        register_call_transfer_for_target(
            context,
            tcx,
            &request,
            concrete_target,
            Some(receiver),
            false,
        )?;
    Ok(())
}

fn closed_covariance_ty(input: ty::Ty<'_>) -> bool {
    !input.has_non_region_param()
        && !input.has_escaping_bound_vars()
        && !input.has_infer()
        && !input.has_placeholders()
        && !input.references_error()
}

fn instance_kind_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, kind: ty::InstanceKind<'tcx>) -> Result<pool_instance::InstanceKind, String> {
    use ty::{InstanceKind as I, ShimKind as S};
    use pool_instance::{InstanceKind as O,ShimKind as H};
    Ok(match kind {
        I::Item(def)=>O::Item { def_id:def_json(context,def) },
        I::Intrinsic(def)=>O::Intrinsic { def_id:def_json(context,def) },
        I::LlvmIntrinsic(def)=>O::LlvmIntrinsic { def_id:def_json(context,def) },
        I::Virtual(def,slot)=>O::Virtual { def_id:def_json(context,def),dispatch_slot:slot },
        I::Shim(shim)=>O::Shim { shim: match shim {
            S::VTable(def)=>H::Vtable { def_id:def_json(context,def) },
            S::Reify(def,reason)=>H::Reify { def_id:def_json(context,def),reason:reason.map(|r|match r {ty::ReifyReason::FnPtr=>"function_pointer",ty::ReifyReason::Vtable=>"vtable"}) },
            S::FnPtr(def,t)=>H::FnPointer {def_id:def_json(context,def),function_type:type_json(context,tcx,t)?},
            S::ClosureOnce {call_once,closure,track_caller}=>H::ClosureOnce {call_once_def_id:def_json(context,call_once),closure_def_id:def_json(context,closure),track_caller},
            S::ConstructCoroutineInClosure {coroutine_closure_def_id,receiver_by_ref}=>H::ConstructCoroutineInClosure {coroutine_closure_def_id:def_json(context,coroutine_closure_def_id),receiver_by_ref},
            S::ThreadLocal(def)=>H::ThreadLocal {def_id:def_json(context,def)},
            S::FutureDropPoll(def,p,i)=>H::FutureDropPoll {def_id:def_json(context,def),proxy_coroutine_type:type_json(context,tcx,p)?,implementation_coroutine_type:type_json(context,tcx,i)?},
            S::DropGlue(def,t)=>H::DropGlue {def_id:def_json(context,def),drop_type:t.map(|t|type_json(context,tcx,t)).transpose()?},
            S::Clone(def,t)=>H::Clone {def_id:def_json(context,def),clone_type:type_json(context,tcx,t)?},
            S::FnPtrAsPtr(def,t)=>H::FnPointerAsPointer {def_id:def_json(context,def),function_type:type_json(context,tcx,t)?},
            S::FnPtrFromPtr(def,t)=>H::FnPointerFromPointer {def_id:def_json(context,def),function_type:type_json(context,tcx,t)?},
            S::AsyncDropGlueCtor(def,t)=>H::AsyncDropGlueConstructor {def_id:def_json(context,def),drop_type:type_json(context,tcx,t)?},
            S::AsyncDropGlue(def,t)=>H::AsyncDropGlue {def_id:def_json(context,def),coroutine_type:type_json(context,tcx,t)?},
        } },
    })
}

fn resolve_callee_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    func: &rustc_middle::mir::Operand<'tcx>,
    call_args: &[rustc_span::Spanned<rustc_middle::mir::Operand<'tcx>>],
    return_destination: ty::Ty<'tcx>,
) -> Result<resolution_values::Callee, String> {
    use resolution_values::{Callee, VirtualResolution};
    let func_ty = func.ty(body, tcx);
    Ok::<_, String>(match *func_ty.kind() {
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
                    {
                        let signature = signature.map_err(|error| {
                            format!("callee signature normalization failed: {error:?}")
                        })?;
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
                            register_runtime_callback_call(
                                context, tcx, body, instance, call_args,
                            )?;
                            register_catch_unwind_intrinsic(
                                context, tcx, instance, body, call_args,
                            )?;
                            register_call_transfer_covariance(
                                context,
                                tcx,
                                body,
                                func_ty,
                                call_args,
                                instance,
                                return_destination,
                            )?;
                            let virtual_resolution = if let ty::InstanceKind::Virtual(def, slot) = instance.def {
                                Some(VirtualResolution { instance_id, method_definition:def_json(context,def), dispatch_slot:slot,
                                    candidate_query_ids:resolution_values::PendingCandidates, selection:"deferred to the runtime receiver vtable" })
                            } else { None };
                            let dispatch_slot = virtual_resolution.as_ref().map(|resolution| resolution.dispatch_slot);
                            let function_type = type_json(context,tcx,func_ty)?;
                            let fn_abi = fn_abi_json(context,tcx,abi)?;
                            if virtual_resolution.is_some() {
                                Callee::VirtualDispatch { function_type, instance_id, dispatch_slot, fn_abi, virtual_resolution }
                            } else {
                                Callee::ResolvedInstance { function_type, instance_id, dispatch_slot, fn_abi, virtual_resolution }
                            }
                        }
                        Err(error) => export_failure(
                            "main::resolve_callee_json",
                            format!(
                                "{}; {}",
                                "resolved_instance_abi_error",
                                format!("{error:?}")
                            ),
                        )?,
                    }
                }
                Ok(None) => export_failure(
                    "main::resolve_callee_json",
                    "unresolved_or_intrinsic_fn_def",
                )?,
                Err(error) => export_failure(
                    "main::resolve_callee_json",
                    format!("{}; {}", "instance_resolution_error", format!("{error:?}")),
                )?,
            }
        }
        ty::FnPtr(..) => {
            if func_ty.has_non_region_param()
                || func_ty.has_escaping_bound_vars()
                || func_ty.has_infer()
                || func_ty.has_placeholders()
            {
                return export_failure("callee resolution",
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
                                return export_failure("callee resolution",
                                    "indirect extra argument types still require caller instantiation",
                                );
                            }
                            match tcx.fn_abi_of_fn_ptr(
                                environment.as_query_input((func_ty.fn_sig(tcx), extra)),
                            ) {
                                Ok(abi) => {
                                    if let Some(request) = call_transfer_request(
                                        tcx,
                                        body,
                                        func_ty,
                                        call_args,
                                        None,
                                        return_destination,
                                    )? {
                                        context.fn_pointer_call_transfers.push(request);
                                    }
                                    Callee::IndirectFunctionPointer {
                                        function_type:type_json(context,tcx,func_ty)?, signature:fn_sig_json_inner(context,tcx,signature)?,
                                        extra_argument_types:extra.iter().map(|ty|type_json(context,tcx,ty)).collect::<Result<Vec<_>,String>>()?,
                                        fn_abi:fn_abi_json(context,tcx,abi)?,
                                    }
                                }
                                Err(error) => export_failure(
                                    "main::resolve_callee_json",
                                    format!(
                                        "{}; {}",
                                        "indirect_function_pointer_abi_error",
                                        format!("{error:?}")
                                    ),
                                )?,
                            }
                        }
                        None => export_failure("callee resolution",
                            "indirect call has fewer arguments than its normalized signature",
                        )?,
                    }
                }
                Err(error) => export_failure(
                    "main::resolve_callee_json",
                    format!(
                        "{}; {}",
                        "indirect_signature_normalization_error",
                        format!("{error:?}")
                    ),
                )?,
            }
        }
        _ => export_failure("main::resolve_callee_json", "indirect_or_non_fn_def")?,
    })
}

fn fn_abi_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    abi: &rustc_target::callconv::FnAbi<'tcx, rustc_middle::ty::Ty<'tcx>>,
) -> Result<u64, String> {
    let (id, fresh) = context.fn_abis.reserve(abi.clone());
    if !fresh {
        return Ok(id as u64);
    }
    let value = pool_layout::FnAbi::new(context, tcx, abi)?;
    context.fn_abis.define(id, value);
    Ok(id as u64)
}

fn const_operand_json<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,body:&rustc_middle::mir::Body<'tcx>,operand:&rustc_middle::mir::ConstOperand<'tcx>)->Result<pool_constant::Operand,String>{
    use pool_constant::{Constant,Annotation,Operand};
    let ty=operand.const_.ty();
    let evaluated=operand.const_.eval(tcx,body.typing_env(tcx),operand.span).map_err(|e|format!("main::const_operand_json: const_evaluation_error; {e:?}"))?;
    let value=const_value_json(context,tcx,ty,evaluated)?;
    Ok(Operand {ty:type_json(context,tcx,ty)?,user_type_annotation:operand.user_ty.map(|a|Annotation::AnnotationRef {index:a.as_u32()}),constant:Constant::EvaluatedConst {value},span:span_json(context,tcx,operand.span)})
}
fn const_value_json<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,ty:ty::Ty<'tcx>,value:rustc_middle::mir::ConstValue)->Result<pool_constant::Value,String>{
    use rustc_middle::mir::ConstValue as C; use pool_constant::Value as O;
    Ok(match value {
        C::ZeroSized=>O::ZeroSized {ty:type_json(context,tcx,ty)?},
        C::Scalar(scalar)=>{
            // Preserve Scalar::Ptr independently of the enclosing type: niche
            // ADTs can carry provenance and must not be converted to integer bits.
            if matches!(*ty.kind(),ty::RawPtr(..)|ty::Ref(..)|ty::FnPtr(..)) || scalar.try_to_scalar_int().is_err() {scalar_pointer_json(context,tcx,ty,scalar)?}
            else {let layout=tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty)).map_err(|_|"main::const_value_json: scalar_layout_unavailable".to_owned())?;let bits=scalar.to_bits(layout.size).report_err().map_err(|e|format!("main::const_value_json: scalar_with_provenance_or_invalid_bits; {e:?}"))?;O::Scalar {ty:type_json(context,tcx,ty)?,bits_unsigned:bits.to_string(),size_bytes:layout.size.bytes()}}
        },
        C::Slice {alloc_id,meta}=>{let allocation=allocation_ref(context,tcx,alloc_id)?; O::SliceAllocation {ty:type_json(context,tcx,ty)?,allocation,metadata_length:meta}},
        C::Indirect {alloc_id,offset}=>{let allocation=allocation_ref(context,tcx,alloc_id)?; O::IndirectAllocation {ty:type_json(context,tcx,ty)?,allocation,offset_bytes:offset.bytes()}},
    })
}

// These are source compiler queries, not conclusions inferred from an
// initializer image, a Rust type spelling or the target triple.
fn static_global_info_json(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> allocation_values::StaticGlobalInfo {
    let nested = match tcx.def_kind(def) {
        rustc_hir::def::DefKind::Static { nested, .. } => nested,
        _ => unreachable!("static global metadata requires a static definition"),
    };
    let global = GlobalAlloc::Static(def);
    let typing_env = ty::TypingEnv::fully_monomorphized();
    let (size, align) = global.size_and_align(tcx, typing_env);
    let mutable = global.mutability(tcx, typing_env);
    allocation_values::StaticGlobalInfo {
        size_bytes: size.bytes(), align_bytes: align.bytes(),
        mutability: match mutable { rustc_ast::Mutability::Mut => "mutable", rustc_ast::Mutability::Not => "immutable" },
        is_static: tcx.is_static(def), is_foreign_item: tcx.is_foreign_item(def), nested,
        thread_local: tcx.is_thread_local_static(def),
    }
}

fn scalar_pointer_json<'tcx>(context:&mut ExportContext<'tcx>,tcx:TyCtxt<'tcx>,ty:ty::Ty<'tcx>,scalar:rustc_middle::mir::interpret::Scalar)->Result<pool_constant::Value,String>{
    use pool_constant::Value as O;
    let (provenance,offset)=scalar.to_pointer(&tcx.data_layout).into_raw_parts();
    Ok(match provenance {
        Some(p)=>{let (alloc_id,immutable,shared_ref)=p.into_parts();let allocation=allocation_ref(context,tcx,alloc_id)?;O::PointerScalar {ty:type_json(context,tcx,ty)?,allocation,offset_bytes:offset.bytes(),immutable,shared_ref}},
        None=>O::PointerScalarWithoutProvenance {ty:type_json(context,tcx,ty)?,address:offset.bytes().to_string(),address_width_bytes:tcx.data_layout.pointer_size().bytes()},
    })
}

fn allocation_ref<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    alloc_id: AllocId,
) -> Result<u64, String> {
    let id = context.allocation_id(alloc_id);
    if context.allocation_ids.definition(id).is_some()
        || context.allocations_in_progress.contains(&alloc_id)
    {
        return Ok(id);
    }
    context.allocations_in_progress.insert(alloc_id);
    use allocation_values::{Allocation, AllocationData as A, VtableEntry as E};
    let data = match tcx.try_get_global_alloc(alloc_id) {
        None => export_failure("main::allocation_ref", "missing_global_allocation")?,
        Some(GlobalAlloc::Memory(memory)) => {
            A::Memory { memory: allocation_memory_payload(context, tcx, memory.inner())? }
        }
        Some(GlobalAlloc::Function { instance }) => {
            context.fn_pointer_targets.insert(instance);
            let instance_id = context.register_instance(instance);
            A::Function { instance_id }
        }
        Some(GlobalAlloc::Static(def)) => {
            let global_info = static_global_info_json(tcx, def);
            let def_id = def_json(context, def);
            let initializer = if tcx.is_foreign_item(def) {
                // Foreign statics have no compiler initializer; querying one ICEs.
                None
            } else {
                Some(allocation_memory_payload(context, tcx,
                    tcx.eval_static_initializer(def).map_err(|error| format!("static initializer: {error:?}"))?.inner())?)
            };
            A::Static { def_id,
                def_path: tcx.def_path_str(def), thread_local: tcx.is_thread_local_static(def), global_info, initializer }
        }
        Some(GlobalAlloc::VTable(ty, predicates)) => {
            context.vtable_diagnostics.record(
                (ty, predicates),
                "symbolic_global",
                None,
                Some(allocator_world::raw_id(alloc_id)),
            );
            let predicate_json = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Result<Vec<_>, String>>()?;
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
                .map(|entry| { Ok::<_, String>(match *entry {
                    ty::VtblEntry::MetadataDropInPlace => {
                        if ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
                            let instance = ty::Instance::resolve_drop_glue(tcx, ty);
                            let instance_id = context.register_instance(instance);
                            E::DropInPlace { instance_id }
                        } else {
                            let instance = ty::Instance::resolve_drop_glue(tcx, ty);
                            // The null vtable entry is not itself invoked as a
                            // vtable function, but dynamic drop resolves this
                            // concrete DropGlue(None), queries its FnAbi and
                            // enters the source shim through find_mir_or_eval_fn.
                            // Register the same full instance/body closure as
                            // other concrete vtable targets while preserving
                            // the source null slot representation below.
                            context.register_vtable_target(instance);
                            E::DropInPlaceNull
                        }
                    }
                    ty::VtblEntry::MetadataSize => {
                        E::SizeBytes
                    }
                    ty::VtblEntry::MetadataAlign => {
                        E::AlignBytes
                    }
                    ty::VtblEntry::Vacant => E::Vacant,
                    ty::VtblEntry::Method(instance) => {
                        let instance_id = context.register_vtable_target(instance);
                        E::Method { instance_id }
                    }
                    ty::VtblEntry::TraitVPtr(trait_ref) => {
                        let existential = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);
                        let vtable_alloc = tcx.vtable_allocation((ty, Some(existential)));
                        E::SupertraitVtablePointer {
                            trait_def_id: def_json(context, trait_ref.def_id),
                            trait_def_path: tcx.def_path_str(trait_ref.def_id),
                            generic_args: generic_args_json(context, tcx, trait_ref.args)?,
                            allocation: allocation_ref(context,tcx,vtable_alloc)?,
                        }
                    }
                }) }).collect::<Result<Vec<_>, String>>()?;
            let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty));
            let (size_bytes, align_bytes) = match layout {
                Ok(layout) => (
                    Some(layout.size.bytes()),
                    Some(layout.align.abi.bytes()),
                ),
                Err(error) => export_failure("vtable layout", format!("{error:?}"))?,
            };
            A::Vtable {
                ty: type_json(context, tcx, ty)?,
                size_bytes: size_bytes.expect("vtable layout"), align_bytes: align_bytes.expect("vtable layout"),
                predicates: predicate_json,
                principal_predicate: predicates.principal().map(|p| existential_predicate_json(context,tcx,p.map_bound(ty::ExistentialPredicate::Trait))).transpose()?,
                entries: entry_json,
            }
        }
        Some(GlobalAlloc::TypeId { ty }) => A::TypeId { ty: type_json(context,tcx,ty)? },
    };
    let node = Allocation { allocation_id: id, source_alloc_id: alloc_id.0.get(), data };
    context.allocations_in_progress.remove(&alloc_id);
    context.allocation_ids.define(id as usize, node);
    Ok(id)
}

fn bound_variable_json(context: &mut ExportContext<'_>, tcx: TyCtxt<'_>, kind: ty::BoundVariableKind<'_>) -> pool_values::BoundVariable {
    use pool_values::{BoundVariable as O, BoundTypeKind as T};
    match kind {
        ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon)=>O::Type {type_kind:T::Anonymous},
        ty::BoundVariableKind::Ty(ty::BoundTyKind::Param(def))=>O::Type {type_kind:T::Parameter {def_id:def_json(context,def)}},
        ty::BoundVariableKind::Region(region)=>O::Region {region_kind:bound_region_kind_json(context,tcx,region)},
        ty::BoundVariableKind::Const=>O::Const,
    }
}

fn existential_predicate_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    predicate: ty::PolyExistentialPredicate<'tcx>,
) -> Result<u64, String> {
    let id = context.predicate_id(predicate);
    if context.predicate_ids.definition(id).is_some() || context.predicates_in_progress.contains(&predicate) {
        return Ok(id);
    }
    context.predicates_in_progress.insert(predicate);
    let payload = allocation_values::Predicate {
        data: existential_predicate_payload_json(context, tcx, predicate)?,
        bound_variables: predicate.bound_vars().iter().map(|bound| bound_variable_json(context, tcx, bound)).collect(),
    };
    context.predicates_in_progress.remove(&predicate);
    context.predicate_ids.define(id as usize, payload);
    Ok(id)
}

// Source interpret/traits.rs::check_vtable_for_type sorts skip_binder values,
// dedups full binders, then normalizes after late-bound-region erasure.
fn compiler_predicate_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    facts: &mut Vec<(u64, u64)>,
) -> Result<(), String> {
    let env = ty::TypingEnv::fully_monomorphized();
    let mut cursor = facts.len();
    while cursor < context.pending_predicates.len() {
        let predicate = context.pending_predicates[cursor];
        let original = existential_predicate_json(context, tcx, predicate)?;
        let erased = tcx.instantiate_bound_regions_with_erased(predicate);
        let normalization = if erased.has_non_region_param()
            || erased.has_escaping_bound_vars()
            || erased.has_infer()
            || erased.has_placeholders()
            || erased.references_error()
        {
            unavailable_compiler_fact(
                "predicate requires complete caller instantiation environment",
            )?
        } else {
            match tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(erased)) {
                Ok(value) => context.predicate_id(ty::Binder::dummy(value)),
                Err(error) => export_failure(
                    "main::compiler_predicate_queries_json",
                    format!(
                        "{}; {}",
                        "predicate normalization failed",
                        format!("{error:?}")
                    ),
                )?,
            }
        };
        facts.push((original, normalization));
        cursor += 1;
    }
    Ok(())
}
fn finish_predicate_queries<'tcx>(tcx: TyCtxt<'tcx>, context: &ExportContext<'tcx>, facts: Vec<(u64, u64)>)
    -> Vec<query_values::PredicateQuery>
{
    let mut records = facts.into_iter().enumerate().map(|(predicate_id, (original, normalization))| {
        query_values::PredicateQuery {
            predicate_id, typing_env: "fully_monomorphized",
            auto_trait: matches!(context.pending_predicates[predicate_id].skip_binder(), ty::ExistentialPredicate::AutoTrait(_)),
            original, normalization, stable_key: 0,
        }
    }).collect::<Vec<_>>();
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
        records[id].stable_key = rank;
        previous = Some(predicate.skip_binder());
    }
    records
}

fn existential_predicate_payload_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    predicate: ty::PolyExistentialPredicate<'tcx>,
) -> Result<allocation_values::PredicateData, String> {
    use allocation_values::{PredicateData as P, ProjectionTerm};
    Ok(match predicate.skip_binder() {
        ty::ExistentialPredicate::Trait(trait_ref) => P::Trait {
            def_id: def_json(context, trait_ref.def_id), def_path: tcx.def_path_str(trait_ref.def_id),
            generic_args: generic_args_json(context,tcx,trait_ref.args)?,
        },
        ty::ExistentialPredicate::AutoTrait(def) => P::AutoTrait { def_id: def_json(context, def), def_path: tcx.def_path_str(def) },
        ty::ExistentialPredicate::Projection(projection) => {
            let term = match projection.term.kind() {
                ty::TermKind::Ty(value) => ProjectionTerm::Type(type_json(context,tcx,value)?),
                ty::TermKind::Const(value) => return export_failure("existential projection", format!("constant projection is not implemented: {value:?}")),
            };
            P::Projection { def_id: def_json(context, projection.def_id), def_path: tcx.def_path_str(projection.def_id),
                generic_args: generic_args_json(context,tcx,projection.args)?, term }
        }
    })
}

fn allocation_memory_payload<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    allocation: &rustc_middle::mir::interpret::Allocation,
) -> Result<allocation_values::Memory, String> {
    let bytes = allocation.inspect_with_uninit_and_ptr_outside_interpreter(0..allocation.len());
    let initialized_ranges = allocation
        .init_mask()
        .range_as_init_chunks(rustc_middle::mir::interpret::AllocRange::from(
            rustc_abi::Size::ZERO..allocation.size(),
        ))
        .map(|chunk| {
            let range = chunk.range();
            allocation_values::InitializationRange {
                state: if chunk.is_init() { "initialized" } else { "uninitialized" },
                start_bytes: range.start.bytes(), end_bytes_exclusive: range.end.bytes(),
            }
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
            let target = allocation_ref(context, tcx, target_alloc)?;
            Ok::<_, String>(allocation_values::Relocation {
                storage_offset_bytes: offset.bytes(), target,
                target_offset_encoded_bytes: bytes_hex(&bytes[start..end]), immutable, shared_ref,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mutability = match allocation.mutability {
        rustc_ast::Mutability::Mut => "mutable",
        rustc_ast::Mutability::Not => "immutable",
    };
    Ok(allocation_values::Memory {
        size_bytes: allocation.size().bytes(), align_bytes: allocation.align.bytes(), mutability,
        byte_image_id: context.byte_images.intern(bytes), initialization_ranges: initialized_ranges, relocations,
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
struct RuntimeTypeFact {
    input_type_id: u64,
    mut_pointer_type: u64,
    mut_reference_type: u64,
    drop_glue: Option<u64>,
}
impl RuntimeTypeFact {
    fn finish(self) -> query_values::RuntimeTypeQuery {
        query_values::RuntimeTypeQuery { input_type_id: self.input_type_id,
            typing_env: "fully_monomorphized", mut_pointer_type: self.mut_pointer_type,
            mut_reference_type: self.mut_reference_type, drop_glue: self.drop_glue }
    }
}
fn compiler_runtime_type_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    processed: &mut HashSet<ty::Ty<'tcx>>,
) -> Result<Vec<RuntimeTypeFact>, String> {
    let mut pending = std::mem::take(&mut context.runtime_type_deferred);
    pending.extend_from_slice(context.runtime_type_query_demands.suffix(context.runtime_type_cursor));
    context.runtime_type_cursor = context.runtime_type_query_demands.len();
    let mut types = Vec::new();
    for input in pending {
        if let Some(id) = context.type_ids.get(&input) {
            types.push((*id, input));
        } else {
            context.runtime_type_deferred.push(input);
        }
    }
    types.sort_by_key(|(id, _)| *id);
    let records=types.into_iter().map(|(id,input)| { {
        processed.insert(input);
        let closed=!input.has_non_region_param() && !input.has_escaping_bound_vars()
            && !input.has_infer() && !input.has_placeholders() && !input.references_error();
        if !closed { return Err(format!("runtime type query requires a closed type: {input:?}")); }
        let normalized=Some(tcx.try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(),ty::Unnormalized::new_wip(input))
            .map_err(|error|format!("runtime type normalization failed for {input:?}: {error:?}"))?);
        let drop=if tcx.lang_items().get(rustc_attr_ir::LangItem::DropGlue).is_none() { None } else { Some(match normalized {
            Some(ty) if tcx.lang_items().get(rustc_attr_ir::LangItem::DropGlue).is_some()=> {
                let instance=ty::Instance::resolve_drop_glue(tcx,ty);
                // rustc represents an empty drop operation as DropGlue(None).
                // Static Drop terminators skip it, so a mere type query does
                // not demand its MIR. Real dynamic/vtable calls promote this
                // identity through register_instance and export the shim body.
                let instance_id=if matches!(instance.def,
                    ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, None))) {
                    let already_reached = context.pending_instances.contains(&instance)
                        || context.emitted_instances.contains(&instance);
                    let id = context.register_instance_identity(instance);
                    if !already_reached {
                        if context.runtime_query_only_empty_drops.insert(instance) {
                            context.note_identity_membership_change(
                                IdentityMembershipSet::RuntimeQueryOnlyEmptyDrop,
                                instance,
                            );
                        }
                    }
                    id
                } else {
                    context.register_instance(instance)
                };
                instance_id
            }
            _=>unavailable_compiler_fact("drop glue requires normalized monomorphic type and drop_in_place lang item")?,
        }) };
        Ok::<_, String>(RuntimeTypeFact { input_type_id:id,
            mut_pointer_type:query_generated_type_json(context,tcx,ty::Ty::new_mut_ptr(tcx,input))?,
            mut_reference_type:query_generated_type_json(context,tcx,ty::Ty::new_mut_ref(tcx,tcx.lifetimes.re_erased,input))?,
            drop_glue: drop })
    } }).collect::<Result<Vec<_>, String>>()?;
    Ok(records)
}

struct VirtualFact {
    original_instance_id: u64,
    method_definition: u64,
    parent_trait: u64,
    concrete_type: u64,
    rebased_args: Vec<pool_values::GenericArgument>,
    resolved: u64,
    vtable_query: query_values::PendingVtableRef,
}
impl VirtualFact {
    fn finish(self, ids: &HashMap<(u64, Vec<u64>), u64>)
        -> Result<query_values::RuntimeVirtualQuery<query_values::VtableRef>, String>
    {
        Ok(query_values::RuntimeVirtualQuery { typing_env: "fully_monomorphized",
            original_instance_id: self.original_instance_id,
            method_definition: self.method_definition, parent_trait: self.parent_trait,
            concrete_type: self.concrete_type, rebased_args: self.rebased_args,
            resolved: self.resolved, vtable_query: self.vtable_query.finish(ids)? })
    }
}
fn compiler_runtime_virtual_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    // call.rs::assert_virtual_instance_matches_concrete: preserve original
    // complete virtual args and use rustc from_assoc/erase_self_ty/rebase_onto.
    let mut state = std::mem::take(&mut context.virtual_state);
    let instance_end = context.instance_ids.len();
    for index in state.instances..instance_end {
        let instance = *context.instance_ids.key(index).unwrap();
        if let ty::InstanceKind::Virtual(def, _) = instance.def {
            state.virtuals.push((index as u64, instance, def));
        }
    }
    state.instances = instance_end;
    let allocation_end = context.allocation_ids.len();
    for index in state.allocations..allocation_end {
        let alloc = *context.allocation_ids.key(index).unwrap();
        if let Some(GlobalAlloc::VTable(input, predicates)) = tcx.try_get_global_alloc(alloc) {
            context.vtable_query_requests.insert((input, predicates));
        }
    }
    state.allocations = allocation_end;
    let targets = context.vtable_query_requests.len();
    // Ensure identities only for the new concrete prefix.
    for index in state.frontier.targets..targets {
        let (input, predicates) = *context.vtable_query_requests.get_index(index).unwrap();
        context.type_id(input);
        for predicate in predicates.iter() { context.predicate_id(predicate); }
    }
    let virtual_count = state.virtuals.len();
    for site in state.frontier.site_start(targets)..virtual_count {
        let (original_instance_id, original, def) = state.virtuals[site];
        // call.rs::eval_fn_call obtains the runtime receiver's dynamic tail,
        // validates the vtable predicates against that exact receiver trait,
        // and only then indexes that trait's vtable. `Self` in a Virtual
        // instance is the statically known receiver type (which may be a
        // DispatchFromDyn wrapper), so use the same codegen tail operation.
        let receiver_ty = original.args.type_at(0);
        let receiver_tail =
            tcx.struct_tail_for_codegen(receiver_ty, ty::TypingEnv::fully_monomorphized());
        let receiver_predicates = match receiver_tail.kind() {
            ty::Dynamic(predicates, _) => Some(predicates),
            _ => None,
        };
        let slot = match original.def {
            ty::InstanceKind::Virtual(_, slot) => slot,
            _ => unreachable!(),
        };
        for target in state.frontier.target_start(site)..targets {
            let (concrete, predicates) = *context.vtable_query_requests.get_index(target).unwrap();
            let predicate_match = receiver_predicates
                .map(|expected| vtable_predicates_match(tcx, expected, predicates))
                .transpose()?;
            if matches!(
                predicate_match.as_ref(),
                Some(VtablePredicateMatch::Mismatch)
            ) {
                // Miri's check_vtable_for_type rejects this candidate before
                // it reads any method slot. It is not a runtime virtual query
                // result and must not create synthetic instances/types.
                continue;
            }
            let parent = tcx.parent(def);
            let trait_ref = ty::TraitRef::from_assoc(tcx, parent, original.args);
            let existential = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref);
            let rebound = original.args.rebase_onto(
                tcx,
                parent,
                existential.with_self_ty(tcx, concrete).args,
            );
            let input_type = type_json(context, tcx, concrete)?;
            let input_type_id = context.type_id(concrete);
            let input_predicates = predicates
                .iter()
                .map(|predicate| existential_predicate_json(context, tcx, predicate))
                .collect::<Result<Vec<_>, String>>()?;
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
            let slot_target = match (receiver_predicates, predicate_match.as_ref()) {
                (Some(expected), Some(VtablePredicateMatch::Match)) => {
                    expected.principal().and_then(|principal| {
                        let principal = tcx.instantiate_bound_regions_with_erased(principal);
                        tcx.vtable_entries(principal.with_self_ty(tcx, concrete))
                            .get(slot)
                            .copied()
                            .and_then(|entry| match entry {
                                ty::VtblEntry::Method(instance) => Some(instance),
                                _ => None,
                            })
                    })
                }
                _ => None,
            };
            let resolved = if receiver_predicates.is_none() {
                unavailable_compiler_fact("virtual receiver type does not have a dynamic tail")?
            } else if slot_target.is_none() {
                unavailable_compiler_fact("validated virtual vtable slot is not a method entry")?
            } else if closed {
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
                        let actual = slot_target.expect("checked above");
                        if instance != actual {
                            export_failure(
                                "main::compiler_runtime_virtual_queries_json",
                                "resolved virtual target differs from the validated vtable slot",
                            )?
                        } else {
                            let id = context.register_vtable_target(instance);
                            state.resolved.insert((original, concrete, instance));
                            id
                        }
                    }
                    Ok(None) => unavailable_compiler_fact(
                        "rustc virtual target resolution returned no instance",
                    )?,
                    Err(error) => export_failure(
                        "main::compiler_runtime_virtual_queries_json",
                        format!(
                            "{}; {}",
                            "rustc virtual target resolution failed",
                            format!("{error:?}")
                        ),
                    )?,
                }
            } else {
                unavailable_compiler_fact(
                    "virtual target query requires complete monomorphic arguments",
                )?
            };
            state.rows.push(VirtualFact {
                original_instance_id, method_definition:def_json(context,def), parent_trait:def_json(context,parent),
                concrete_type:input_type, rebased_args:generic_args_json(context,tcx,rebound)?, resolved,
                vtable_query:query_values::PendingVtableRef { input_type:type_json(context,tcx,concrete)?,
                    input_predicates, key:(input_type_id,input_predicate_ids) } });
        }
    }
    state.frontier.complete(virtual_count, targets);
    let sites = context.virtual_call_transfers.len();
    let targets = state.resolved.len();
    for site in state.transfers.site_start(targets)..sites {
        for target in state.transfers.target_start(site)..targets {
            let (original, concrete, instance) = *state.resolved.get_index(target).unwrap();
            register_virtual_call_transfers(context, tcx, original, concrete, instance, site)?;
        }
    }
    state.transfers.complete(sites, targets);
    context.virtual_state = state;
    Ok(())
}

enum VtablePredicateMatch {
    Match,
    Mismatch,
}

/// Mirror interpret/traits.rs::check_vtable_for_type. A mismatch is a
/// source-level invalid-vtable outcome; a normalization failure aborts export.
fn vtable_predicates_match<'tcx>(
    tcx: TyCtxt<'tcx>,
    expected: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    actual: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> Result<VtablePredicateMatch, String> {
    let mut expected: Vec<_> = expected.without_auto_traits().collect();
    let mut actual: Vec<_> = actual.without_auto_traits().collect();
    expected.sort_by(|a, b| a.skip_binder().stable_cmp(tcx, &b.skip_binder()));
    actual.sort_by(|a, b| a.skip_binder().stable_cmp(tcx, &b.skip_binder()));
    expected.dedup();
    actual.dedup();
    if expected.len() != actual.len() {
        return Ok(VtablePredicateMatch::Mismatch);
    }

    let env = ty::TypingEnv::fully_monomorphized();
    for (expected, actual) in expected.into_iter().zip(actual) {
        let expected = tcx.instantiate_bound_regions_with_erased(expected);
        let actual = tcx.instantiate_bound_regions_with_erased(actual);
        let expected = match tcx
            .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(expected))
        {
            Ok(value) => value,
            Err(error) => return Err(format!("vtable predicate normalization failed: {error:?}")),
        };
        let actual = match tcx.try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(actual))
        {
            Ok(value) => value,
            Err(error) => return Err(format!("vtable predicate normalization failed: {error:?}")),
        };
        if expected != actual {
            return Ok(VtablePredicateMatch::Mismatch);
        }
    }
    Ok(VtablePredicateMatch::Match)
}

#[derive(serde::Serialize)]
struct CallerInstance {
    instance_id: u64,
    requires_caller_location: bool,
    display: String,
    inline_never: bool,
    target_features: Vec<TargetFeature>,
    is_foreign_item: bool,
    is_closure_like: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    intrinsic_metadata: Option<Option<IntrinsicMetadata>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    item_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    codegen_symbol_name: Option<Option<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    symbol_name: Option<String>,
}
#[derive(serde::Serialize)]
struct TargetFeature {
    name: String,
    kind: &'static str,
}
#[derive(serde::Serialize)]
struct FrameMetadata {
    local_crate: u32,
    crates: Vec<CrateMetadata>,
}
#[derive(serde::Serialize)]
struct CrateMetadata {
    #[serde(rename = "crate")]
    krate: u32,
    name: String,
}
fn compiler_caller_location_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &ExportContext<'tcx>,
) -> Result<Vec<CallerInstance>, String> {
    let mut instances = context
        .instance_ids
        .iter()
        .filter(|(instance, _)| !context.symbol_only_instances.contains(instance))
        .map(|(instance, id)| (*id, *instance))
        .collect::<Vec<_>>();
    instances.sort_by_key(|(id, _)| *id);
    let mut records = Vec::new();
    for (id, instance) in instances {
        let mut row = CallerInstance {
            instance_id: id,
            requires_caller_location: instance.def.requires_caller_location(tcx),
            display: instance.to_string(),
            inline_never: matches!(
                tcx.codegen_instance_attrs(instance.def).inline,
                rustc_attr_ir::InlineAttr::Never
            ),
            target_features: tcx
                .codegen_instance_attrs(instance.def)
                .target_features
                .iter()
                .map(|feature| TargetFeature {
                    name: feature.name.as_str().to_owned(),
                    kind: match feature.kind {
                        rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Implied => {
                            "implied"
                        }
                        rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Enabled => {
                            "enabled"
                        }
                        rustc_middle::middle::codegen_fn_attrs::TargetFeatureKind::Forced => {
                            "forced"
                        }
                    },
                })
                .collect(),
            is_foreign_item: tcx.is_foreign_item(instance.def_id()),
            is_closure_like: tcx.is_closure_like(instance.def_id()),
            intrinsic_metadata: None,
            item_name: None,
            codegen_symbol_name: None,
            symbol_name: None,
        };
        // These compiler APIs have narrower domains than Instance itself.
        // Virtual dispatch has no standalone codegen symbol; the runtime
        // resolves its actual vtable target before requesting a symbol.
        if matches!(
            tcx.def_kind(instance.def_id()),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            row.intrinsic_metadata = Some(intrinsic_metadata_json(tcx, instance.def_id())?);
        }
        if let Some(name) = tcx.opt_item_name(instance.def_id()) {
            row.item_name = Some(name.as_str().to_owned());
        }
        if tcx.def_kind(instance.def_id()).has_codegen_attrs() {
            row.codegen_symbol_name = Some(
                tcx.codegen_fn_attrs(instance.def_id())
                    .symbol_name
                    .map(|symbol| symbol.as_str().to_owned()),
            );
        }
        if !matches!(instance.def, ty::InstanceKind::Virtual(..)) {
            if instance.args.has_non_region_param()
                || instance.args.has_escaping_bound_vars()
                || instance.args.has_infer()
                || instance.args.has_placeholders()
            {
                return Err(format!(
                    "symbol query requires closed instance: {instance:?}"
                ));
            }
            row.symbol_name = Some(tcx.symbol_name(instance).name.to_owned());
        }
        records.push(row);
    }
    Ok(records)
}

fn compiler_frame_metadata_json(tcx: TyCtxt<'_>) -> FrameMetadata {
    let local = rustc_hir::def_id::LOCAL_CRATE;
    let mut crates = tcx.crates(()).iter().copied().collect::<Vec<_>>();
    crates.push(local);
    crates.sort_by_key(|krate| krate.as_u32());
    crates.dedup();
    FrameMetadata {
        local_crate: local.as_u32(),
        crates: crates
            .into_iter()
            .map(|krate| CrateMetadata {
                krate: krate.as_u32(),
                name: tcx.crate_name(krate).as_str().to_owned(),
            })
            .collect(),
    }
}

// FnAbiOf::fn_abi_of_instance. Complete instance+extra-argument vector+env is
// the query key; empty arguments are also recorded for runtime drop/vtable calls.
#[derive(Clone, serde::Serialize)]
struct InstanceAbi { typing_env:&'static str, instance_id:u64, extra_argument_types:Vec<u64>, abi_query:u64 }
struct InstanceAbiFact {
    instance_id: u64,
    extra_argument_types: Vec<u64>,
    abi_query: u64,
}
impl InstanceAbiFact {
    fn finish(self) -> InstanceAbi {
        InstanceAbi { typing_env: "fully_monomorphized", instance_id: self.instance_id,
            extra_argument_types: self.extra_argument_types, abi_query: self.abi_query }
    }
}
fn compiler_instance_abis_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    let mut state = std::mem::take(&mut context.abi_state);
    let mut requests = OrderedSet::default();
    requests.extend(context.instance_abi_requests.suffix(state.explicit).iter().copied());
    state.explicit = context.instance_abi_requests.len();
    let event_end = context.instance_events.len();
    for index in state.events..event_end {
        let instance = &context.instance_events[index];
        if context.runtime_query_only_empty_drops.contains(instance)
            || context.metadata_only_instances.contains(instance)
        {
            continue;
        }
        // A VTable shim can be registered merely by serializing a vtable
        // entry. That preserves compiler identity, but is not itself a call
        // site and does not establish an FnAbi demand. In particular, querying
        // FnOnce::call_once for a `&FnOnce` vtable shim under the global
        // fully-monomorphized environment can ICE while normalizing its
        // associated Output projection. A real MIR call inserts its exact
        // `(instance, extra_args)` request above, which remains in `requests`.
        if matches!(
            instance.def,
            ty::InstanceKind::Shim(ty::ShimKind::VTable(_))
        ) {
            continue;
        }
        if !matches!(
            tcx.def_kind(instance.def_id()),
            rustc_hir::def::DefKind::Fn
                | rustc_hir::def::DefKind::AssocFn
                | rustc_hir::def::DefKind::Ctor(_, rustc_hir::def::CtorKind::Fn)
                | rustc_hir::def::DefKind::Closure
                | rustc_hir::def::DefKind::SyntheticCoroutineBody
        ) {
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
    state.events = event_end;
    let requests = requests.into_iter().filter(|key| state.completed.insert(*key)).collect::<Vec<_>>();
    let records=requests.into_iter().map(|(instance,extra)|{ {
        let closed=!instance.args.has_non_region_param() && !instance.args.has_escaping_bound_vars()
            && !instance.args.has_infer() && !instance.args.has_placeholders()
            && !extra.has_non_region_param() && !extra.has_escaping_bound_vars()
            && !extra.has_infer() && !extra.has_placeholders();
        let function=matches!(tcx.def_kind(instance.def_id()),rustc_hir::def::DefKind::Fn|rustc_hir::def::DefKind::AssocFn|rustc_hir::def::DefKind::Ctor(_, rustc_hir::def::CtorKind::Fn)|rustc_hir::def::DefKind::Closure|rustc_hir::def::DefKind::SyntheticCoroutineBody);
        let abi=if matches!(instance.def,ty::InstanceKind::LlvmIntrinsic(_)){
            unavailable_compiler_fact("source FnAbi query is not defined for LLVM intrinsic instances")?
        }else if !closed || !function {
            unavailable_compiler_fact("FnAbi instance query requires a complete monomorphic function instance and extra argument vector")?
        }else{match tcx.fn_abi_of_instance(ty::TypingEnv::fully_monomorphized().as_query_input((instance,extra))){
                Ok(abi)=>compiler_fact(fn_abi_json(context,tcx,abi)?),
            Err(error)=>export_failure("main::compiler_instance_abis_json", format!("{}; {}", "rustc fn_abi_of_instance failed", format!("{error:?}")))?,
        }};
        let record=InstanceAbiFact { instance_id:context.register_metadata_instance(instance), extra_argument_types:extra.iter().map(|ty| type_json(context,tcx,ty)).collect::<Result<Vec<_>, String>>()?, abi_query:abi };
        Ok::<_, String>(record)
    } }).collect::<Result<Vec<_>, String>>()?;
    state.rows.extend(records);
    context.abi_state = state;
    Ok(())
}

// backtrace.rs::handle_miri_get_backtrace and resolve_frame_pointer. The table
// covers compiler-produced frame positions only. Forged/unseen byte positions
// require additional source-map evidence; consumers must never guess a line.
fn backtrace_spans_json<'tcx>(context: &mut ExportContext<'tcx>, tcx: TyCtxt<'tcx>, body: &rustc_middle::mir::Body<'tcx>) -> Vec<pool_body::BacktraceSpan> {
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
            pool_body::BacktraceSpan {
                span: span_json(context, tcx, span),
                source_position: pool_body::SourcePosition {
                    byte_position: collapsed.lo().0, line: position.line,
                    zero_based_char_column: position.col.0,
                    filename: context.files.intern(position.file.name.prefer_remapped_unconditionally().to_string()),
                },
            }
        })
        .collect::<Vec<_>>();
    records
}

// interpret/discriminant.rs and Ty::{discriminant_ty,discriminant_for_variant}.
fn discriminant_facts_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
) -> Result<pool_type::Discriminants, String> {
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
                return export_failure(
                    "discriminants",
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
    Ok(pool_type::Discriminants {
        has_discriminants: values.is_some(),
        adt_variant_count: count,
        values: values
            .unwrap_or_default()
            .into_iter()
            .map(|(index, d)| {
                Ok(pool_type::Discriminant {
                    variant: index.as_u32(),
                    ty: type_json(context, tcx, d.ty)?,
                    bits: d.val.to_string(),
                })
            })
            .collect::<Result<_, String>>()?,
    })
}

fn discriminant_type_fact_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
) -> Result<u64, String> {
    Ok::<_, String>(match input.kind() {
        ty::UnsafeBinder(bound) => {
            let inner = tcx.instantiate_bound_regions_with_erased((*bound).into());
            if inner.has_escaping_bound_vars() || inner.has_non_region_param() {
                return export_failure(
                    "discriminant type",
                    "unsafe-binder discriminant query retains bound type/const variables",
                );
            }
            discriminant_type_fact_json(context, tcx, inner)?
        }
        ty::Pat(base, _) => discriminant_type_fact_json(context, tcx, *base)?,
        _ => type_json(context, tcx, input.discriminant_ty(tcx))?,
    })
}

// interpret/traits.rs::get_vtable_ptr, before source salt/reservation effects.
fn compiler_vtable_metadata_json<'tcx>(
    context: &mut ExportContext<'tcx>,
    tcx: TyCtxt<'tcx>,
    input: ty::Ty<'tcx>,
    predicates: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
) -> Result<query_values::VtableMetadata, String> {
    let predicate_json = predicates
        .iter()
        .map(|predicate| existential_predicate_json(context, tcx, predicate))
        .collect::<Result<Vec<_>, String>>()?;
    let principal = predicates
        .principal()
        .map(|principal| tcx.instantiate_bound_regions_with_erased(principal));
    let entries = if let Some(principal) = principal {
        tcx.vtable_entries(principal.with_self_ty(tcx, input))
    } else {
        TyCtxt::COMMON_VTABLE_ENTRIES
    };
    let entry_json=entries.iter().map(|entry|{ Ok::<_, String>(match *entry {
        ty::VtblEntry::MetadataDropInPlace=>if input.needs_drop(tcx,ty::TypingEnv::fully_monomorphized()) {
            let instance=ty::Instance::resolve_drop_glue(tcx,input);
            let instance_id=context.register_instance(instance);
            allocation_values::VtableEntry::DropInPlace { instance_id }
        }else{
            let instance=ty::Instance::resolve_drop_glue(tcx,input);
            // Dynamic drop performs the same concrete call sequence as the
            // ordinary vtable serializer above, even when the vtable's drop
            // slot is null for `needs_drop == false`.
            context.register_vtable_target(instance);
            allocation_values::VtableEntry::DropInPlaceNull
        },
        ty::VtblEntry::MetadataSize=>allocation_values::VtableEntry::SizeBytes,
        ty::VtblEntry::MetadataAlign=>allocation_values::VtableEntry::AlignBytes,
        ty::VtblEntry::Vacant=>allocation_values::VtableEntry::Vacant,
        ty::VtblEntry::Method(instance)=>{
            let instance_id=context.register_vtable_target(instance);
            allocation_values::VtableEntry::Method { instance_id }
        },
        ty::VtblEntry::TraitVPtr(trait_ref)=>{
            let existential=ty::ExistentialTraitRef::erase_self_ty(tcx,trait_ref);
            let allocation=tcx.vtable_allocation((input,Some(existential)));
            // `vtable_allocation` returns rustc's internal memory allocation
            // for a TraitVPtr. It need not be exposed as `GlobalAlloc::VTable`,
            // so close the exact target query from the compiler edge itself.
            // This is the same concrete type and erased principal used to
            // obtain `allocation`; it is not a guessed supertrait relation.
            let child_predicate =
                ty::Binder::dummy(ty::ExistentialPredicate::Trait(existential));
            let child_predicates = tcx.mk_poly_existential_predicates(&[child_predicate]);
            context
                .vtable_query_requests
                .insert((input, child_predicates));
            context.vtable_diagnostics.record((input, child_predicates), "trait_vptr",
                Some((input, predicates)), None);
            allocation_values::VtableEntry::SupertraitVtablePointer { trait_def_id:def_json(context,trait_ref.def_id), trait_def_path:tcx.def_path_str(trait_ref.def_id), generic_args:generic_args_json(context,tcx,trait_ref.args)?, allocation:allocation_ref(context,tcx,allocation)? }
        },
    }) }).collect::<Result<Vec<_>, String>>()?;
    let (size_bytes, align_bytes) =
        match tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(input)) {
            Ok(layout) => (
                Some(layout.size.bytes()),
                Some(layout.align.abi.bytes()),
            ),
            Err(error) => export_failure("vtable layout", format!("{error:?}"))?,
        };
    Ok(query_values::VtableMetadata { r#type:type_json(context,tcx,input)?, size_bytes, align_bytes,
        predicates:predicate_json,
        principal_predicate:predicates.principal().map(|p| existential_predicate_json(context,tcx,p.map_bound(ty::ExistentialPredicate::Trait))).transpose()?,
        entries:entry_json })
}

struct VtableFact {
    input_type: u64,
    input_predicates: Vec<u64>,
    output_type: u64,
    output_predicates: Vec<u64>,
    output_type_monomorphic_enough: bool,
    output_predicates_monomorphic_enough: bool,
    vtable_allocation: Option<AllocId>,
    vtable_metadata: query_values::VtableMetadata,
}
fn compiler_vtable_queries_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
) -> Result<(), String> {
    let mut state = std::mem::take(&mut context.vtable_state);
    let allocation_end = context.allocation_ids.len();
    for index in state.allocations..allocation_end {
        let alloc = *context.allocation_ids.key(index).unwrap();
        if let Some(GlobalAlloc::VTable(input, predicates)) = tcx.try_get_global_alloc(alloc) {
            context.vtable_query_requests.insert((input, predicates));
            context.vtable_diagnostics.record(
                (input, predicates),
                "symbolic_global",
                None,
                Some(allocator_world::raw_id(alloc)),
            );
        }
    }
    state.allocations = allocation_end;
    loop {
        // cast.rs::unsize_into_ptr validates the source vtable's concrete
        // type, then get_vtable_ptr(ty, destination_predicates) constructs a
        // destination vtable for that same type. Candidate source vtables are
        // the exact compiler requests and globals already reached by MIR;
        // recursively discovered TraitVPtr requests join on later rounds.
        let upcast_end = context.dynamic_vtable_upcast_requests.len();
        let source_end = context.vtable_query_requests.len();
        for site in state.upcasts.site_start(source_end)..upcast_end {
            let (source_tail, target_tail) = *context.dynamic_vtable_upcast_requests.get_index(site).unwrap();
            let (ty::Dynamic(source_predicates, _), ty::Dynamic(target_predicates, _)) =
                (source_tail.kind(), target_tail.kind())
            else { continue; };
            for target in state.upcasts.target_start(site)..source_end {
                let (concrete, actual_predicates) = *context.vtable_query_requests.get_index(target).unwrap();
                if matches!(
                    vtable_predicates_match(tcx, source_predicates, actual_predicates)?,
                    VtablePredicateMatch::Match
                ) {
                    let demand = (concrete, *target_predicates);
                    context.vtable_query_requests.insert(demand);
                    context.vtable_diagnostics.upcast_demand(
                        demand,
                        (concrete, actual_predicates),
                        source_tail,
                        target_tail,
                    );
                }
            }
        }
        state.upcasts.complete(upcast_end, source_end);
        let request_end = context.vtable_query_requests.len();
        if state.requests == request_end { break; }
        let pending = context.vtable_query_requests.suffix(state.requests).to_vec();
        state.requests = request_end;
        for (input, predicates) in pending {
            let input_json = type_json(context, tcx, input)?;
            let input_type_id = context.type_id(input);
            let mut input_predicates = Vec::new();
            let mut input_predicate_ids = Vec::new();
            for predicate in predicates.iter() {
                input_predicate_ids.push(context.predicate_id(predicate));
                input_predicates.push(existential_predicate_json(context, tcx, predicate)?);
            }
            let (output, erased) = tcx.erase_and_anonymize_regions((input, predicates));
            // Runtime get_vtable_ptr reserves by this canonical pair. Its
            // later vtable_entries lookup therefore needs query metadata
            // keyed by the erased/anonymized identities as well as the
            // original compiler request. Re-query only the actual rustc
            // result; the normal closure makes an idempotent pair a no-op.
            if (output, erased) != (input, predicates) {
                let canonical = (output, erased);
                context.vtable_query_requests.insert(canonical);
                context.vtable_diagnostics.record(
                    canonical,
                    "canonical_output",
                    Some((input, predicates)),
                    None,
                );
            }
            let output_json = type_json(context, tcx, output)?;
            let output_type_id = context.type_id(output);
            let output_predicates = erased
                .iter()
                .map(|p| existential_predicate_json(context, tcx, p))
                .collect::<Result<Vec<_>, String>>()?;
            let output_predicate_ids = erased
                .iter()
                .map(|p| context.predicate_id(p))
                .collect::<Vec<_>>();
            let vtable_metadata = compiler_vtable_metadata_json(context, tcx, input, predicates)?;
            // A vtable query row can describe a vtable that is referenced by
            // a TraitVPtr entry yet is serialized only as its memory image.
            // Preserve the exact rustc global-allocation identity that the
            // entry's `allocation_ref` uses. Do not allocate a new exporter
            // graph ID here: a missing mapping means this row is not a
            // serialized target identity, and consumers must not guess one.
            let vtable_allocation = predicates.principal().map(|principal| {
                let principal = tcx.instantiate_bound_regions_with_erased(principal);
                tcx.vtable_allocation((input, Some(principal)))
            });
            let ordering = (
                input_type_id,
                input_predicate_ids.clone(),
                output_type_id,
                output_predicate_ids,
            );
            let row = VtableFact { input_type:input_json,
                input_predicates, output_type:output_json, output_predicates,
                output_type_monomorphic_enough:!output.has_param(), output_predicates_monomorphic_enough:!erased.has_param(),
                vtable_allocation, vtable_metadata };
            state.rows.push((ordering, (input_type_id, input_predicate_ids), row));
        }
    }
    context.vtable_state = state;
    Ok(())
}

fn finish_vtable_queries(mut facts: Vec<((u64, Vec<u64>, u64, Vec<u64>), (u64, Vec<u64>), VtableFact)>, context: &ExportContext<'_>)
    -> (Vec<query_values::VtableQuery>, HashMap<(u64, Vec<u64>), u64>)
{
    facts.sort_by(|left, right| left.0.cmp(&right.0));
    let mut query_ids = HashMap::new();
    let records = facts.into_iter().enumerate().map(|(query_id, (_, key, fact))| {
        query_ids.insert(key, query_id as u64);
        query_values::VtableQuery {
            query_id: query_id as u64,
            input_type: fact.input_type, input_predicates: fact.input_predicates,
            output_type: fact.output_type, output_predicates: fact.output_predicates,
            output_type_monomorphic_enough: fact.output_type_monomorphic_enough,
            output_predicates_monomorphic_enough: fact.output_predicates_monomorphic_enough,
            vtable_allocation_id: fact.vtable_allocation.and_then(|id| context.allocation_ids.get(&id).copied()),
            vtable_metadata: fact.vtable_metadata,
        }
    }).collect();
    (records, query_ids)
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
#[derive(serde::Serialize)]
struct IntrinsicMetadata { must_be_overridden: bool, fallback_is_spec: bool }
fn intrinsic_metadata_json(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> Result<Option<IntrinsicMetadata>, String> {
    if !matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn) {
        return unavailable_compiler_fact("intrinsic query requires a function definition");
    }
    Ok(tcx.intrinsic(def).map(|info| IntrinsicMetadata { must_be_overridden: info.must_be_overridden, fallback_is_spec: intrinsic_fallback_is_spec(tcx,def) }))
}

// step.rs::eval_fn_call: normalized original signature for arity/ExternAbi,
// original FnPtr binder plus exact ordered extra argument types for FnAbi.
#[derive(serde::Serialize)]
struct FunctionFacts {
    types: Vec<FunctionTypeFact>,
    pointer_abis: Vec<PointerAbi>,
    helper_signatures: Vec<HelperSignature>,
}
#[derive(serde::Serialize)]
struct FunctionTypeFact {
    type_id: u64,
    typing_env: &'static str,
    function_kind: FunctionKind,
    signature_query: pool_type::FunctionSignature,
}
#[derive(serde::Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum FunctionKind {
    FunctionPointer,
    FunctionDefinition { instance_id: u64 },
}
#[derive(serde::Serialize)]
struct PointerAbi {
    type_id: u64,
    typing_env: &'static str,
    extra_argument_types: Vec<u64>,
    abi_query: u64,
}
#[derive(serde::Serialize)]
struct HelperSignature {
    typing_env: &'static str,
    signature: pool_type::FunctionSignature,
    splatted: bool,
    abi_query: u64,
}
// Only semantic results are retained during discovery. Query rows are assembled
// after all producer frontiers are exhausted.
#[derive(Default)]
struct FunctionDiscovery<'tcx> {
    type_cursor: usize,
    request_cursor: usize,
    types: BTreeMap<u64, (Option<u64>, pool_type::FunctionSignature)>,
    completed_abis: HashSet<(ty::Ty<'tcx>, &'tcx ty::List<ty::Ty<'tcx>>)>,
    abis: Vec<(u64, Vec<u64>, u64)>,
    helper_signatures: HashSet<ty::FnSig<'tcx>>,
    helpers: Vec<(pool_type::FunctionSignature, u64)>,
}
impl FunctionDiscovery<'_> {
    fn finish(self) -> FunctionFacts {
        FunctionFacts {
            types: self.types.into_iter().map(|(type_id, (instance, signature))| FunctionTypeFact {
                type_id, typing_env: "fully_monomorphized",
                function_kind: match instance {
                    Some(instance_id) => FunctionKind::FunctionDefinition { instance_id },
                    None => FunctionKind::FunctionPointer,
                },
                signature_query: signature,
            }).collect(),
            pointer_abis: self.abis.into_iter().map(|(type_id, extra_argument_types, abi_query)| PointerAbi {
                type_id, typing_env: "fully_monomorphized", extra_argument_types, abi_query,
            }).collect(),
            helper_signatures: self.helpers.into_iter().map(|(signature, abi_query)| HelperSignature {
                typing_env: "fully_monomorphized", signature, splatted: false, abi_query,
            }).collect(),
        }
    }
}
fn compiler_function_facts_json<'tcx>(
    tcx: TyCtxt<'tcx>,
    context: &mut ExportContext<'tcx>,
    state: &mut FunctionDiscovery<'tcx>,
) -> Result<(), String> {
    loop {
        let mut requests = OrderedSet::default();
        requests.extend(context.fn_pointer_abi_requests.suffix(state.request_cursor).iter().copied());
        state.request_cursor = context.fn_pointer_abi_requests.len();
        for (input, extra) in requests.iter().copied() {
            context.type_id(input);
            for input in extra.iter() { context.type_id(input); }
        }
        let type_end = context.type_ids.len();
        let pending = (state.type_cursor..type_end)
            .map(|id| (id as u64, *context.type_ids.key(id).unwrap()))
            .filter(|(_, input)| matches!(input.kind(), ty::FnDef(..) | ty::FnPtr(..)))
            .collect::<Vec<_>>();
        state.type_cursor = type_end;
        let helper_inputs = pending.clone();
        for (id, input) in pending {
            if matches!(input.kind(), ty::FnPtr(..)) { requests.insert((input, ty::List::empty())); }
            let closed = !input.has_non_region_param()
                && !input.has_escaping_bound_vars()
                && !input.has_infer()
                && !input.has_placeholders();
            let signature = if !closed {
                unavailable_compiler_fact(
                    "function signature requires a complete monomorphic type",
                )?
            } else {
                match tcx.try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    ty::Unnormalized::new_wip(input.fn_sig(tcx)),
                ) {
                    Ok(sig) => compiler_fact(fn_sig_json_inner(
                        context,
                        tcx,
                        tcx.instantiate_bound_regions_with_erased(sig),
                    )?),
                    Err(error) => export_failure(
                        "main::compiler_function_facts_json",
                        format!(
                            "{}; {}",
                            "function signature normalization failed",
                            format!("{error:?}")
                        ),
                    )?,
                }
            };
            let kind = match *input.kind() {
                ty::FnPtr(..) => None,
                ty::FnDef(def, args) => Some( context.register_metadata_instance(ty::Instance {
                        def: ty::InstanceKind::Item(def),
                        args: args.skip_binder(),
                    }),
                ),
                _ => unreachable!(),
            };
            state.types.insert(id, (kind, signature));
        }
    let abis=requests.into_iter().filter(|key| state.completed_abis.insert(*key)).map(|(input,extra)|{ {
        let closed=!input.has_non_region_param() && !input.has_escaping_bound_vars() && !input.has_infer() && !input.has_placeholders()
            && !extra.has_non_region_param() && !extra.has_escaping_bound_vars() && !extra.has_infer() && !extra.has_placeholders();
        let abi=if !closed {unavailable_compiler_fact("FnPtr ABI requires a complete monomorphic function type and extra argument vector")?}
        else{match tcx.fn_abi_of_fn_ptr(ty::TypingEnv::fully_monomorphized().as_query_input((input.fn_sig(tcx),extra))){
            Ok(abi)=>compiler_fact(fn_abi_json(context,tcx,abi)?),
            Err(error)=>export_failure("main::compiler_function_facts_json", format!("{}; {}", "rustc fn_abi_of_fn_ptr failed", format!("{error:?}")))?,
        }};
        Ok::<_, String>((context.type_id(input), extra.iter().map(|ty| type_json(context,tcx,ty)).collect::<Result<Vec<_>, String>>()?, abi))
    } }).collect::<Result<Vec<_>, String>>()?;
        state.abis.extend(abis);
    // helpers.rs::call_function constructs a Safe, nonvariadic, unsplatted
    // dummy-binder signature from actual argument/output types. Query exact
    // constructor candidates; adapters must match every request field.
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
                    if !state.helper_signatures.insert(signature) {
                        continue;
                    }
                    let result = match tcx.fn_abi_of_fn_ptr(
                        ty::TypingEnv::fully_monomorphized()
                            .as_query_input((ty::Binder::dummy(signature), ty::List::empty())),
                    ) {
                        Ok(abi) => compiler_fact(fn_abi_json(context, tcx, abi)?),
                        Err(error) => export_failure(
                            "main::compiler_function_facts_json",
                            format!(
                                "{}; {}",
                                "helper dummy signature ABI query failed",
                                format!("{error:?}")
                            ),
                        )?,
                    };
                    state.helpers.push((fn_sig_json_inner(context, tcx, signature)?, result));
                }
            }
        }
    }
        if state.type_cursor == context.type_ids.len()
            && state.request_cursor == context.fn_pointer_abi_requests.len()
        {
            break;
        }
    }
    Ok(())
}

#[cfg(test)]
mod instance_demand_tests {
    use super::*;

    fn item() -> ty::Instance<'static> {
        ty::Instance {
            def: ty::InstanceKind::Item(rustc_hir::def_id::DefId {
                krate: rustc_hir::def_id::LOCAL_CRATE,
                index: rustc_hir::def_id::DefIndex::from_u32(0),
            }),
            args: ty::List::empty(),
        }
    }

    #[test]
    fn metadata_and_symbol_discovery_orders_preserve_the_same_query_demands() {
        let instance = item();
        let mut metadata_first = ExportContext::default();
        let id = metadata_first.register_metadata_instance(instance);
        assert_eq!(metadata_first.register_metadata_instance(instance), id);
        assert!(metadata_first.metadata_only_instances.contains(&instance));
        assert_eq!(metadata_first.register_instance_identity(instance), id);

        let mut symbol_first = ExportContext::default();
        assert_eq!(symbol_first.register_instance_identity(instance), id);
        assert_eq!(symbol_first.register_metadata_instance(instance), id);
        assert_eq!(symbol_first.register_metadata_instance(instance), id);

        assert_eq!(metadata_first.instance_ids.iter().collect::<HashMap<_, _>>(), symbol_first.instance_ids.iter().collect::<HashMap<_, _>>());
        assert_eq!(metadata_first.metadata_only_instances, symbol_first.metadata_only_instances);
        assert_eq!(metadata_first.symbol_only_instances, symbol_first.symbol_only_instances);
        assert_eq!(metadata_first.identity_membership_delta, symbol_first.identity_membership_delta);
        assert!(!metadata_first.metadata_only_instances.contains(&instance));
        assert!(metadata_first.symbol_only_instances.contains(&instance));
        assert!(metadata_first.pending_instances.is_empty());
    }

    #[test]
    fn symbol_and_real_upgrades_signal_fixpoint_changes_without_allocating_another_id() {
        let instance = item();
        let mut context = ExportContext::default();
        let id = context.register_metadata_instance(instance);
        context.identity_membership_delta.clear();
        assert_eq!(context.register_instance_identity(instance), id);
        assert!(context.identity_membership_delta.contains(&(IdentityMembershipSet::MetadataOnly, instance)));
        assert!(context.pending_instances.is_empty());
        context.identity_membership_delta.clear();
        assert_eq!(context.register_instance(instance), id);
        assert!(!context.symbol_only_instances.contains(&instance));
        assert!(context.identity_membership_delta.contains(&(IdentityMembershipSet::SymbolOnly, instance)));
        assert_eq!(context.pending_instances, vec![instance]);
        context.identity_membership_delta.clear();
        let completed_events = context.instance_events.len();
        assert_eq!(context.register_metadata_instance(instance), id);
        assert_eq!(context.register_instance_identity(instance), id);
        assert_eq!(context.instance_events.len(), completed_events);
        assert!(context.identity_membership_delta.is_empty());
        assert!(!context.metadata_only_instances.contains(&instance));
        assert!(!context.symbol_only_instances.contains(&instance));
        assert_eq!(context.instance_ids.len(), 1);

        let mut direct = ExportContext::default();
        direct.register_metadata_instance(instance);
        direct.identity_membership_delta.clear();
        assert_eq!(direct.register_instance(instance), id);
        assert!(direct.identity_membership_delta.contains(&(IdentityMembershipSet::MetadataOnly, instance)));
        assert!(direct.identity_membership_delta.contains(&(IdentityMembershipSet::SymbolOnly, instance)));
    }
}

#[cfg(test)]
mod snapshot_writer_tests {
    use super::*;
    struct Refuse;
    impl serde::Serialize for Refuse {
        fn serialize<S: serde::Serializer>(&self, _: S) -> Result<S::Ok, S::Error> {
            Err(serde::ser::Error::custom("injected serialization failure"))
        }
    }
    #[test]
    fn failed_serialization_keeps_the_previous_snapshot() {
        let directory = env::temp_dir().join(format!("lean-miri-writer-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("snapshot.json");
        fs::write(&path, b"previous snapshot").unwrap();
        assert!(
            write_document(&path, &Refuse)
                .unwrap_err()
                .contains("injected serialization failure")
        );
        assert_eq!(fs::read(&path).unwrap(), b"previous snapshot");
        #[derive(serde::Serialize)]
        struct Finished {
            query_id: u64,
        }
        write_document(&path, &Finished { query_id: 7 }).unwrap();
        assert_eq!(fs::read_to_string(&path).unwrap(), "{\"query_id\":7}");
        fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod extern_abi_tests {
    use super::*;

    #[test]
    fn kind_and_unwind_preserve_every_pinned_rustc_abi() {
        let mut spellings = HashMap::new();
        for abi in rustc_abi::ExternAbi::ALL_VARIANTS {
            let wire = extern_abi_json(*abi);
            assert_eq!(spellings.insert((wire.kind, wire.unwind), abi.as_str()), None);
        }
        assert_ne!(extern_abi_json(rustc_abi::ExternAbi::C { unwind: false }).kind,
                   extern_abi_json(rustc_abi::ExternAbi::System { unwind: false }).kind);
        assert_ne!(extern_abi_json(rustc_abi::ExternAbi::C { unwind: false }).unwind,
                   extern_abi_json(rustc_abi::ExternAbi::C { unwind: true }).unwind);
    }
}
