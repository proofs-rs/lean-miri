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
bodies. Selecting a generic definition directly is an error.

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

The root schema is `lean-miri-rustc-mir` version 6. Evaluated integer scalars carry
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
| `definitions` | Compiler `DefId` (crate and definition index) |
| `type_constants` | Compiler `Const`, including its type and constructor |
| `predicates` | Full bound existential predicate; comparison rank is separate |
| `bodies` | Instance, promoted index and source/query mode |

The Rust collector uses one `Pool<K, D>` implementation for the ten compiler identity tables. The additional `files` table interns strings.
Each compiler key `K` owns its reserved index and a single concrete semantic
value `D`, such as `pool_layout::Layout`, `pool_type::Type` or `pool_body::Body`.
Nested fields are Rust records, enums, optional values and typed references;
collection does not store JSON trees in these pools. Serialization converts the
completed values to JSON when assembling the output document.

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
Generic arguments remain in their owning records, with type and type-constant
references into the corresponding tables. `body_roots` records root metadata and
body IDs. Each concrete instance and promoted index identifies one executable
body, with generic arguments substituted, types normalized and constants
evaluated before export. Roots and instance records reference that same body.
Generic templates are not executable inputs; normalization or constant-evaluation
failures abort export, including unused required constants. Diagnostic spans and
scopes remain attached to the resolved instructions.
This is a breaking wire-format change: earlier source/normalization-body
snapshots must be regenerated. The reader requires each body's concrete
`instance_id` and evaluated constants; it does not support the earlier shape.
[Decoder](../Miri/Input/Decoder.lean) validates typed-table and query contracts.
Successful query results are serialized directly: booleans remain booleans,
optional results use JSON null, and structured results carry their semantic
fields. There are no success-status wrappers or completeness flag. Lean validates
required fields, semantic tags and references before returning an execution input.
An ID is reserved before its definition is traversed, so mutually recursive
references do not require a table ordering. Export fails if a reserved definition
is unfinished. Lean indexes source ranges, decodes compiler pools, and constructs interpreter
MIR directly while reading bodies. It retains typed query records, checks
reference bounds and keeps IDs through execution; it does not retain a generic
JSON tree or an intermediate MIR value tree. Runtime lookups return checked errors.
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
