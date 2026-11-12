# MIR exporter

Exports structured MIR, monomorphized instances, types, physical layouts, ABIs,
allocation graphs, and query information for statics/TLS/vtables and other
entities from the pinned rustc_private. See the
[development guide](../docs/development.md#rust-toolchain-and-reference-setup)
for pinned versions and setup.

```bash
export CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export MIRI_SYSROOT="$PWD/scratch/miri-sysroot"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d build --locked --manifest-path exporter/Cargo.toml
mkdir -p scratch/exports
exporter/target/debug/lean-miri-mir-exporter --output scratch/exports/add-one.json \
  --root add_one -- exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
ELAN_HOME="$PWD/.elan" .elan/bin/lake build check_input
ELAN_HOME="$PWD/.elan" .elan/bin/lake exe check_input scratch/exports/add-one.json
```

`check_input` diagnoses readiness; it does not execute a guest or prove safety.
See [CheckInput.lean](../tools/CheckInput.lean) for actual arguments and exit
classifications. Import into Lean constants uses the experimental `import_mir`
in `Miri.Frontend.ImportMIR`. A minimal executable client-generation example
is in [check_import.py](../tests/frontend/check_import.py); canonical configuration
and terminal-check examples are in [connected tests](../tests/connected/README.md).

`--root` specifies an exact nongeneric local def-path. Without it, closed local
bodies are roots. Generic definitions enter the graph through their actual
monomorphic instances; unsubstituted templates are not exported as executable
bodies. Covered generic instances instead reference shared typed source templates
that Lean instantiates when the body is requested. Selecting a generic definition
directly is an error.

Every requested semantic query must succeed. Missing MIR, failed normalization,
layout or ABI queries, unavailable initializers and incomplete producer evidence
abort the export with a nonzero exit status. No failed query is serialized as a
payload that a consumer might later accept. Target and execution demand determine
which queries apply; pure `no_std` and `no_core` roots do not request OS startup
or foreign-shim catalogs. Successful `false`, `None` and empty query results
retain their meaning. Diagnostic debug payloads remain separate.

For Cargo projects, use `exporter/target/debug/lean-miri-mir-exporter --cargo check
--manifest-path /path/to/Cargo.toml`. The wrapper uses pinned Cargo/rustc,
rebuilds dependency crates with MIR, writes target-crate JSON under `lean-miri-mir/`
in the target directory, and continues ordinary metadata/codegen. It uses
`MIRI_SYSROOT` for the target and optional `MIRI_HOST_SYSROOT` for host
build tools/proc macros. Host tools use the pinned compiler and are not exported.
Response-file invocations fail closed because their
exact arguments cannot be fingerprinted.

## Input contract

The producer writes `lean-miri-rustc-mir` version 12. Evaluated integer scalars carry
`bits_unsigned` and the compiler layout's `size_bytes`, so consumers can construct
the machine scalar before reading the type and layout tables. Zero-sized and
pointer constants retain their separate representations. Compiler values have
separate tables with document-local, dense, zero-based IDs:

| Table | Interning key |
| --- | --- |
| `types` | Exact rustc `Ty`, retaining binders and regions |
| `layouts` | Complete `TyAndLayout`, including field and variant layouts |
| `fn_abis` | Complete `FnAbi`, including argument layouts and passing modes |
| `instances` | Exact rustc `InstanceKind` and its local generic arguments |
| `allocations` | Compiler `AllocId`, independently of memory contents |
| `spans` | Compiler `Span`, including its hygiene context |
| `files` | Exact filename spelling (string values, shared across spans and backtraces) |
| `byte_images` | Exact immutable byte vector (shared storage, independent allocation identities) |
| `definitions` | Compiler `DefId` (crate and definition index) |
| `type_constants` | Compiler `Const`, including its type and constructor |
| `predicates` | Full bound existential predicate; comparison rank is separate |
| `bodies` | Instance, promoted index and source/query mode |
| `mir_templates` | Generic definition and promoted index, within the supported source-body category |

ABI rows store `return` and each `arguments` entry as an index into
`abi_arguments`. The explicit `Initial` passing-mode recipe reconstructs
`ArgAbi::new` from the physical layout with empty scalar attributes in Lean.
The producer selects this recipe only when the complete final rustc mode equals
that initial constructor; target-adjusted modes retain their explicit payload.
For primitive nonpointer scalar layouts on 64-bit x86_64, `ScalarRust`,
`ScalarSysvArgument` and `ScalarSysvReturn` instead derive scalar `NoUndef`
attributes and integer extensions in Lean. The SysV recipes cover canonical C
on targets that are neither Windows nor Darwin; ordinary Rust uses its boolean
extension rule. The producer checks the reconstructed mode against rustc and
fails export on disagreement. Pointer attributes, aggregates, other target
classifiers and complete FnAbi query resolution remain compiler results.
These rules follow pinned [`arg_attrs_for_rust_scalar`](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_ty_utils/src/abi.rs#L318)
and the checked-in `rustc_target::callconv` sources.
`FnAbi` rows also require `unwind_seed`: the original external ABI, optional
source-definition `NEVER_UNWIND`/foreign-item/drop-glue flags, and the effective
panic and panic-in-drop policies. Lean evaluates pinned `fn_can_unwind` from
these materials. The old `can_unwind` result field is rejected. Coroutine,
closure and thread-local shim signatures follow the source instance signature
rules; per-row producer checks compare the material's source decision with the
queried rustc ABI. This seed does not replace the remaining FnAbi query.
Already concrete primitive/tuple signatures for ordinary item instances and
function pointers carry `signature_seed` with original input/output types,
ordered variadic extras and optional caller-location type. Such rows omit
`fixed_count`: Lean plans argument construction and derives that count, then
checks the physical argument vector. Signature type normalization remains an
explicit dependency (structural identity or a residual normalization leaf).
Rows requiring other instance signature rewrites retain a residual `fixed_count`;
exactly one construction representation is required.
Each payload contains the complete type and layout;
sharing requires equality of all three, including all mode attributes.

The Rust collector uses one `Pool<K, D>` implementation for the ten compiler identity tables. The additional `files` and `byte_images` tables intern exact strings and byte vectors.
Each compiler key `K` owns its reserved index and a single concrete semantic
value `D`, such as `pool_layout::Layout`, `pool_type::Type` or `pool_body::Body`.
Nested fields are Rust records, enums, optional values and typed references;
collection does not store JSON trees in these pools. Serialization converts the
completed values to JSON when assembling the output document.

The allocation wire array groups function allocations with the same Instance into
one payload and an `identities` array of `[graph_id, source_alloc_id]` pairs.
Other allocation kinds retain their individual identities. Every memory payload,
including static and thread-local initializers, stores a `byte_image_id`; size,
alignment, initialization, relocations and provenance flags remain independent.
Prepared-world `raw_pool` positions imply source ID `index + 1`: null slots join
their unique serialized allocation, while opaque and dangling globals retain
explicit exceptional rows. Dedup salt arrays carry graph IDs in salt order;
source IDs and byte keys come from those allocations. All 32 outcomes remain
required for function, vtable and byte keys. The reader accepts only schema 13 inputs.

Schema 12 requires `compiler_coroutine_coverage`, including an explicit Boolean
marker for every executable body. A marked body owns one complete, normalized
coroutine witness: kind, erased yield/resume fields, saved-local types and source
information, state-to-field mappings, variant sources and storage conflicts.
The saved-local `source_info` uses the existing source-info pool. Missing or
unknown witnesses and unlowered executable terminators fail closed. Schema 11
forbids the new table; its maintained input bytes remain unchanged.

Coroutine auxiliary MIR uses a separate owner/role table, retaining the compiler's
actual source kind and snapshot phase. It never becomes a callable body merely
because an async/proxy snapshot shares the resume function's source identity.
Callable drop shims still come from the exact `instance_mir` query. The reader
checks owner/source/role/phase links, full selected physical variant layouts and
saved-state field types/layouts. Root tag queries retain their compiler-produced
narrowed scalar layout. These rules follow the pinned compiler's
[StateTransform](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_mir_transform/src/coroutine/mod.rs),
[drop snapshots](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_mir_transform/src/coroutine/drop.rs)
and [canonical shim construction](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_mir_transform/src/shim.rs).
This metadata coverage does not establish general coroutine execution support.

Schema 11 uses exact-equality payload pools without changing compiler identity.
`layouts` is an array of indices into `layout_values`: a type's `layout` still
indexes `layouts`, so equal physical payloads retain separate `LayoutId`s.
Type `boolean_queries` fields index root `boolean_queries`, and non-null
`discriminants` fields index root `discriminants`; null remains explicit.
Every memory payload's `initialization_ranges` and `relocations` fields index
root arrays of arrays with those names. Bodies index root `backtrace_spans`;
statement `kind` fields index `statement_kinds`; MIR `source_info` fields index
`source_infos`. Source information remains separate from statement kinds so
sharing a statement does not merge its use sites. Pool payloads retain all
false values, null values and empty arrays. Lean resolves forward references
independently of root field order and checks contextual bounds at each use.

Maintained historical fixtures were mechanically projected from schema 8 with
`tools/shared_json_pools.py`; the inverse projection preserves every retained
JSON value. Schema 11 removes body diagnostics unused by Lean, local debug info,
mutability and redundant layouts, and source-scope local data. `required_consts`
remains present. The exporter rejects tainted MIR before collecting any body,
including promoted bodies. Span `ctxt` contains its original rustc debug text as
a string. `tests/fixtures/shared-pools-projection.json` pins both file hashes
and the original and retained canonical expanded hashes. Connected reference sidecars preserve the
original reference snapshot binding under `wire_projection`; this transformation
does not constitute a new compiler export or Miri execution.

Discovery retains compiler query results until the reachable graph closes.
Append-only request domains have consumer cursors; pair consumers visit new sites
against all targets and old sites against new targets, including negative query
results. Instance eligibility changes notify dependent consumers. Signature,
predicate, allocation-byte, and identity collectors retain their completed facts.
After convergence, read-only finalization builds query rows, orders vtable queries,
resolves their final allocation references, and assigns predicate comparison ranks.
Pool serialization stays in discovery when it can reveal another compiler key;
output projection does not create keys or rerun discovery.

References are numeric indices interpreted by the field's schema. Span `file` and
backtrace `source_position.filename` reference the global `files` string table.
Span filenames retain rustc's debug spelling; backtrace filenames retain its
remapped display spelling. Distinct spellings remain distinct, even when they
refer to the same source file. Lean retains these IDs through decoding and
preparation and resolves text only when displaying diagnostics or serving the
guest backtrace filename query. Layouts retain
exact compiler `TyAndLayout` keys, including field and variant layouts. Allocation
IDs retain compiler allocation identity even when bytes are equal. IDs are local
to the document; exported `source_alloc_id` records the separate raw Miri AllocId.
Schema 8 stores ABI argument attributes only as `regular_bits`, argument extension,
and pointee size/alignment. Boolean attributes and capture mode are derived from
those bits. External ABIs retain their structured `kind` and `unwind`; their
canonical source spelling is not stored. ADT representation stores `flags_bits`,
integer, alignment, packing and scalable-element data, rather than boolean views
of those values. Type compiler facts use the owning `type_id` and optional
`layout_query_input_type`; an absent layout-query input means the owning type.
This preserves a distinct region-erased query input when one exists.
Backtrace `source_position.byte_position` is the body-specific collapsed position;
it can differ from the global span's position for an inlined body.
The reader accepts only the current producer schema. Explicit array offsets retain their count,
width and per-field equality checks. The producer stores array offsets as an
exact stride/count formula, and represents a resolved LLVM intrinsic call with
`kind: "llvm_intrinsic"`, `function_type` and `instance_id`, without `fn_abi`.
Only an exact `LlvmIntrinsic` compiler identity may use that form. Normal,
virtual and indirect calls still require an ordinary ABI. LLVM dispatch retains
its intrinsic signature, argument, feature and memory checks; unknown intrinsics
remain Unsupported. LLVM-ABI function-pointer signatures and layouts are retained
as metadata, but have no ordinary ABI row. Synthetic LLVM-ABI helper candidates
are omitted while their valid Rust-ABI candidates remain. An actual LLVM-ABI
function-pointer call fails export explicitly before the compiler's undefined
ABI query; ordinary function-pointer queries remain required. Older wire
versions must be regenerated with the current producer.

Generic arguments remain in their owning records, with type and type-constant
references into the corresponding tables. `body_roots` records root metadata and
body IDs. Each body row has an explicit `body_kind`. A `material` row contains
the compiler's instantiated executable MIR and evaluated constants. A
`copy_template` row contains only `template_id`, `instance_id`, generic arguments
and promoted-body references. Its shared `mir_templates` source contains a typed
instruction skeleton, local type-expression slots and diagnostic source metadata.
It contains no monomorphic fallback body. Metadata preparation inspects these
seeds without instantiating executable MIR; `SourceMir.resolveBody` substitutes
arguments, erases free regions in its supported binder-free domain and resolves
exact type identities on demand. Missing source capabilities fail that demand.
The pure resolver keeps no body-answer cache across executions.

The source-template category currently covers ordinary generic item bodies with
unprojected local copy/move operations, tuple/array aggregates, storage markers,
goto/switch/return/unreachable terminators and supported binder-free source type
constructors. Calls, drops, constant operands, compiler shims and unsupported
actual argument constructors retain the explicit `material` category. Category
selection happens before instantiation; failure after selecting a template is
an error. Diagnostic spans and scopes remain attached to resolved instructions.
This is a breaking wire-format change: earlier snapshots must be regenerated.
[Decoder](../Miri/Input/Decoder.lean) validates typed-table and query contracts.
Successful query results are serialized directly: booleans remain booleans,
optional results use JSON null, and structured results carry their semantic
fields. There are no success-status wrappers or completeness flag. Lean validates
required fields, semantic tags and references before returning an execution input.
An ID is reserved before its definition is traversed, so mutually recursive
references do not require a table ordering. Export fails if a reserved definition
is unfinished. Lean indexes source ranges, decodes compiler pools, and constructs interpreter
MIR directly while reading material bodies, and retains typed source templates
for lazy body resolution. It retains typed query records, checks reference bounds
and keeps IDs through execution; it does not retain a generic JSON tree.
Runtime lookups return checked errors.
Malformed table definitions are reported before downstream scope validation.

Covariance collection has two phases. During source-demand closure, explicit
MIR/call-transfer requests and reached vtable receiver requests serialize their
endpoint types. Serialization retains recursive query-demand suppression for
query-generated types, while allowing their definitions and referenced compiler
data to complete the export closure. Relation answers do not drive that closure.
After convergence, a read-only pass groups all closed pool types by normalized
identity and combines the distinct ordered pairs in each group with the demanded
pairs. Exact compiler-type equality deduplicates requests; existing numeric type
IDs order the rows. Each pair is evaluated once with rustc's covariant relation,
including successful false answers, before allocation-world capture. Normalization
failure still aborts export, but is reported during this final pass. The schema
and query meaning are unchanged; document-local ID assignment can change.

A successful export describes the requested compiler data. Runtime values, including a
virtual call's receiver and vtable, still determine execution. Export success is
neither a proof of interpreter correspondence nor a proof of UB freedom.

Specify `LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1` for prepared execution such as
main. Building with `--features miri-reference` and adding
`LEAN_MIRI_RUN_PREPARED_MIRI=1` also generates a reference Miri sidecar by
continuing the same TyCtxt after export. This does not promise the same allocation
history as vanilla Miri. See [connected tests](../tests/connected/README.md) for
the distinction between fresh generation and replay of fixed inputs.

[build.rs](build.rs) and runtime checks verify the rustc commit; on Linux they
also verify the loaded librustc_driver. This boundary fails closed on other OSes.
`tools/exporter_provenance.py --document INPUT --exporter BINARY --manifest OUTPUT`
can record SHA-256 of adjacent inputs, but it does not prove a fully hermetic
build including macros, includes and environment. FNV fingerprints check
consistency and are not cryptographic hashes.

## Tests

After the toolchain and MIR-enabled sysroot setup above, run from the repository
root with the same environment:

```bash
"$CARGO_HOME/bin/cargo" +miri-exporter-8144389c895d test --locked --offline --manifest-path exporter/Cargo.toml
```

The LLVM no-ABI producer fixture is part of that unittest discovery. After a
reference-feature release exporter and `native_runner` build, run
`flock /tmp/lean-miri-ci-guest.lock python3 tests/llvm_no_abi/check.py --output scratch/llvm-controls-new`
for fresh reference/guest controls covering arithmetic and pause through both
C and the actual stdarch LLVM ABI, stdarch AES, missing target
features, argument count, symbol clashes, invalid vector layouts and unknown
intrinsics. The latter rejection/Unsupported controls are never counted as safe
guest execution. `tests/input/LlvmCallEvidence.lean` takes a fresh export of
`exporter/fixtures/fail_closed/llvm_no_abi.rs` (`--root identity`) and checks strict
ABI evidence validation, current pooled-fixture acceptance, and rejection of
older root schema versions.

This runs the Rust unit tests, Python unittest discovery under `exporter/tests/`,
all four `test-*.sh` fixture scripts, and four producer checks, using Cargo's
executable for the selected
profile and target directory. Failures include the child process output. Fixture
tests require bash, Python 3, the pinned toolchain and a matching MIR-enabled
sysroot; missing prerequisites fail with setup instructions rather than skip.
Run `bash tools/setup-rustc-exporter.sh` and `bash tools/setup-miri-reference.sh`
from the repository root to prepare them (see the development guide).

The shell scripts remain available for focused checks. `test-fixture.sh` also
calls the variadic and call-transfer scripts, preserving its standalone coverage;
Cargo additionally exposes those two as individually selectable tests. For example,
append `--test suites call_transfer_fixture` to the Cargo command above. Cargo
passes `EXPORTER_BIN` so fixture scripts do not rebuild the exporter; standalone
scripts can also use this override. Each fixture uses temporary output directories.

The producer checks cover input settings and consumed artifact hashes, exact
u128/niche ranges, function/vtable allocator-world crosswalks, and static/TypeId
crosswalks. Their validators live under `exporter/`. The allocator-world Rust
fixtures shared with Lean input checks live under `tests/fixtures/`. Run one
with `--test suites producer_settings`, `primitive_ranges`, `selected_alloc_world`
or `selected_static_typeid`. For standalone use, after building the exporter,
run `bash exporter/tests/run-producer.sh NAME` (`settings` selects the settings
check). An optional second argument supplies an output JSON path; the Lean
primitive-range driver uses this to consume the same checked export.

Lean decoder, frontend and execution comparisons under root `tests/` remain
separate integration checks; this command does not run the entire repository suite.

Prepared allocator snapshots distinguish complete byte-memory keys from
`non_exhaustive_key_families`: function, vtable, static, TypeId, and general
constant-memory keys. This is coverage metadata, not a failed query result.
Every imported function/vtable/static/TypeId global must have its exact selected
key outcome; functions and vtables require all 32 salts. The decoder rejects
missing keys or truncated salts, and runtime lookup rejects keys outside the
validated selected domain. Unrequested compiler globals may reserve opaque raw
IDs, but cannot point to an imported or failed semantic allocation. General
constant-memory keys have no selected-key support; requests remain explicit
runtime errors. This snapshot contract does not assert completeness of arbitrary
runtime key discovery. Salt rows record the actual dedup allocation identities in
the prepared post-export TCX; they do not record whether a lookup populated a
previously absent entry. Snapshot and closure sentinels remain reserved source
IDs, and the final sentinel fixes the next runtime allocation ID.

After building the pinned exporter and Lean decoder, this boundary check uses a
fresh prepared snapshot (not a saved historical input):

```sh
EXPORTER_BIN=exporter/target/release/lean-miri-mir-exporter \
  bash exporter/tests/run-producer.sh selected_alloc_world scratch/selected-keys.json
lake env lean --run tests/input/SelectedKeyCoverageStrict.lean scratch/selected-keys.json
lake env lean --run tests/input/AllocWorldRuntime161.lean scratch/selected-keys.json
```
