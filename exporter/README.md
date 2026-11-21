# MIR exporter

The pinned rustc frontend exports a structural closure of concrete MIR instances,
evaluated constants and finite compiler material. Lean uses that material to
compute layout, ABI, trait and vtable queries during execution. Generic function
MIR is not exported or instantiated by Lean. See the
[development guide](../docs/development.md#rust-toolchain-and-reference-setup)
for the pinned compiler and MIR-enabled standard library.

After setup, run from the repository root:

```bash
bash tools/build-exporter.sh
mkdir -p scratch/exports
bash tools/export-mir.sh --output scratch/exports/add-one.json --root add_one -- \
  exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
ELAN_HOME="$PWD/.elan" .elan/bin/lake build check_input
ELAN_HOME="$PWD/.elan" .elan/bin/lake exe check_input scratch/exports/add-one.json
```

`check_input` checks input acceptance; it neither executes the guest nor proves
safety. `import_mir` in `Miri.Frontend.ImportMIR` reflects accepted typed input
into closed Lean constants. See the [main guide](../README.md) for execution and
the [connected tests](../tests/connected/README.md) for expected-result checks.

## Roots and concrete reachability

`--root` selects an exact local def-path and may be repeated. An executable with
no explicit roots selects its entry function; libraries require a root list.
A generic root contributes `root_declarations` metadata without a body.
Concrete instances discovered from executable roots enter the ordinary body
closure. Unselected generic definitions do not contribute function MIR.

The closure follows every basic block, rather than only one diagnostic execution.
Direct calls, function-pointer casts and constant relocations register concrete
instances. Vtable constructors register concrete method and drop instances;
supertraits, dynamic upcasts and generated shims can extend that closure.
Available external-crate MIR is traversed in the same way as local MIR. Missing
required MIR stops export, so dependencies and std must contain compatible MIR.
The collector does not rely solely on code-generation mono items.

Compiler identities, executable bodies and source-material demands remain
distinct. An identity used only as metadata does not automatically demand a
body. Source discovery can reveal further executable instances, so the collector
closes these domains together. It does not build layout/ABI/covariance answers
for arbitrary combinations of all known types and functions.

Each executable body is keyed by a concrete instance and promoted index.
Intrinsic, virtual and foreign identities retain their dispatch kind rather than
requiring an ordinary MIR body. rustc substitutes a body's
generic arguments, normalizes the MIR and evaluates constants, including unused
required constants, before serialization. Remaining type/const parameters,
normalization failures, unavailable initializers and unfinished references stop
export. Ordinary recursion reuses the instance key; deduplication alone does not
prove termination when fresh concrete instantiations keep appearing.

## Source input

The producer and reader use `lean-miri-rustc-mir` schema 17. Earlier versions
require fresh export. Each type carries a `validation_rank`. At import, Lean
checks that normalization and by-value children descend. References do not add
their pointee as a by-value child. The validity visitor orders a selected enum
variant before its enclosing enum and a synthetic scalar field before a wide
pointer of the same type. Unpacking a dynamic place starts a sized traversal.
The execution document contains no layout, FnAbi or
covariance answer tables. Table IDs are dense and local to one document;
allocation source IDs retain a separate raw identity. Source spans include the source-map
expansion position used by caller-location intrinsics, and session material
retains the location-detail policy. Lean constructs each caller location when
the intrinsic executes; the exporter does not preallocate a Location for every
span. Its new prepared allocation history is compared with Miri under the same
preparation, rather than preserving the former eager-hook history.

| Material | Contents and consumer |
| --- | --- |
| `bodies`, `instances`, `body_roots` | Concrete MIR, compiler instance identities, call/cast references and selected executable roots |
| `types` | Concrete type structure, substituted ADT fields and variants, repr, discriminants, normalization references, lang-item flags and declaration attributes |
| `runtime_target_data_layout`, `source_abi` | Target geometry and ABI policy, normalized callable signatures, function attributes |
| `source_trait_material` | Relevant trait/impl declarations, generic type patterns, clauses, ADT tails and associated-type bounds |
| `source_vtables` | Instantiated object-trait method/supertrait graph and concrete drop/method instance bindings |
| `source_cast_targets` | Resolution witnesses for actual function-pointer and closure casts |
| `allocations`, `byte_images` | Evaluated constant memory and symbolic compiler allocations, with distinct identities, initialization and provenance |
| `definitions`, `type_constants`, `predicates` | Referenced compiler identities and normalized finite declaration material |
| `files`, `spans`, shared payload arrays | Exact source positions, remapped runtime filenames and shared payloads used by MIR and memory |
| `syntax_contexts`, `expansions` | Finite hygiene declarations used by Lean to collapse a span relative to its body |
| `compiler_session_queries` | Target/session settings, including caller-location file/line/column redaction |

Concrete ADT field types and repr drive Lean layout calculation. Generic type
patterns are retained where trait selection, potentially-unsized tails or
associated-type bounds need them. This does not introduce generic function MIR
or a runtime function-body substitution phase. Coroutine auto traits use the
pre-cleanup witness fields and ignore flags; the optimized state layout can
retain a different field set. Coroutine `Unpin` follows declared movability.
Layout, ABI and trait algorithms
consume the decoded typed records; runtime-created arrays and pointer types use
the same query implementation.

The input boundary checks tags, scalar widths, declaration scopes, identities,
local MIR bounds and references, then returns typed `ExecutionInput`. It retains
neither a generic JSON tree nor a second MIR tree. The file entrypoint currently
reads a complete `String`. Lean execution uses only the input and its own state;
it starts no compiler process and uses no cache shared between executions.
Unsupported algorithms and missing runtime material remain explicit errors.

The expansion position is trusted rustc source-map material: macro expansion,
path remapping and display columns are resolved during export. Lean applies the
session redaction policy and computes the Location layout, bytes, initialization
and provenance when the intrinsic executes. Filename bytes include a trailing
NUL in storage; the string length excludes it. Existing compiler byte/salt dedup
state supplies filename identity, and each invocation reserves a fresh Location
root. Passing a track-caller span between frames does not itself allocate one.

Backtraces collapse expansion chains in Lean from typed context IDs, call-site
spans and collapse attributes. The exporter projects the private rustc collapse
attribute through its public single-step API; it emits no body/span answer table.
Source-map coordinates and remapped filenames remain trusted compiler material.
Frame positions are resolved at exact known span starts. Other BytePos values
remain unsupported rather than approximated by a nearby source position.
LLVM intrinsic identities retain explicit dispatch without an ordinary FnAbi;
ordinary calls use Lean's ABI calculation and unknown LLVM operations still fail.

## Compiler trust boundary

The input trusts rustc's MIR selection, monomorphization, normalization and
constant evaluation. Declaration and target facts also remain compiler input:
repr and inferred variance, lang-item/type identity, bound-variable flags,
normalized signatures and compiler coroutine state material,
predicate normalization/erasure/order and concrete cast resolution. ABI follows
Miri's `fn_abi_of_instance_no_deduced_attrs` policy; codegen-only parameter-use
summaries are not exported.
Lean computes final layout and ABI values from these inputs, including final
parameter attributes, rather than receiving the compiler's final answer rows.

The instantiated object-trait graph and vtable bindings retain rustc's method
eligibility, concrete resolution, vacancy and drop instances. Lean computes
object graph traversal, slots and runtime metadata from
those bindings and declarations. A vtable already evaluated inside a constant
retains its rustc-produced memory/entries, size and alignment as part of trusted
constant evaluation. This is separate from Lean's runtime vtable calculation.

Constants retain more than value bytes: allocation identity, alignment,
mutability, initialized ranges, relocations, encoded offsets, CTFE provenance
flags and graph sharing/cycles remain explicit. Equal byte images do not merge
allocation identities. IDs are reserved before recursively following references.

`LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1` captures the prepared compiler allocation
world used by ordinary main execution and reference comparisons. Reached
function/vtable keys retain all 32 salted source identities, with selected
static/TypeId keys and the raw-ID frontier. These are trusted finite identity and
address-history facts. They preserve observable allocation distinctions; they
are not a proof of arbitrary runtime constructor coverage or equivalence with
vanilla Miri's allocation history. Missing selected keys and truncated salts are
rejected. Runtime values and allocations are created afresh for each execution.

The exporter trusts that its trait-header inventory and disjoint outer-head
filter retain every relevant implementation; selected clauses and tail heads
extend the material. General instance/material containment, algorithm fidelity
and Rust/interpreter correspondence remain separate proof obligations in
[STATUS.md](../STATUS.md). A successful export or finite comparison is not a
UB-freedom theorem.

## Cargo and reference execution

`lean-miri-mir-exporter --cargo --root main check --manifest-path /path/to/Cargo.toml`
wraps pinned Cargo/rustc and exports selected primary targets. Exporter `--root`
options precede the Cargo subcommand; library targets need explicit roots.
Dependencies are compiled with MIR but do not produce independent exports.
Each invocation uses a fresh retained run directory beneath the Cargo target
directory and prints its location. Repeated Cargo exports include dependency
compilation cost; they do not reuse a prior export-run cache.
The wrapper continues ordinary metadata/codegen. `MIRI_SYSROOT` selects the target sysroot; optional
`MIRI_HOST_SYSROOT` selects the sysroot for build tools and proc macros. Host
tools are not exported. Response-file invocations fail because their exact
arguments cannot be fingerprinted.

With `--features miri-reference`, `LEAN_MIRI_RUN_PREPARED_MIRI=1` continues the
same TyCtxt after export and writes a reference sidecar. It requires the prepared
allocation-world profile. [build.rs](build.rs) and runtime checks verify the
pinned rustc commit and, on Linux, the loaded librustc_driver. Artifact hashes
identify consumed inputs; they do not establish a hermetic build covering every
macro, include and environment dependency.

## Checks

`--oracle-output OTHER.json` writes independent rustc answers for the exact
exported input. Those answers are not part of the execution document or read by
the interpreter. The oracle uses the closed production identities and actual
call operands; it does not extend the body graph or enumerate ABI candidate
combinations. Oracle output cannot be combined with prepared allocation-world
or reference execution: compiler oracle queries can change allocation history.
The comparison driver binds the oracle to the input bytes and
compiler revision before running layout, type-query, ABI and vtable checks:

```bash
bash tools/export-mir.sh --output scratch/exports/add-one.json \
  --oracle-output scratch/exports/add-one-oracle.json --root add_one -- \
  exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
python3 tools/check-source-queries.py \
  scratch/exports/add-one.json scratch/exports/add-one-oracle.json
```

Run Rust units and exporter fixture suites with the pinned environment:

```bash
"$CARGO_HOME/bin/cargo" +miri-exporter-8eb778d04094 test --locked --offline \
  --manifest-path exporter/Cargo.toml
```

Lean integration and theorem checks are separate. `tools/check-empty-function.sh`
checks concrete providers for its fixture and then the kernel theorem/axiom
closure. [STATUS.md](../STATUS.md) records current validation gaps; historical
fixture and CI successes do not establish schema-17 execution. Whole-pipeline
performance comparisons use identical Rust inputs and fixed artifacts via
`tools/measure-pipeline.py`, as described in [PROFILING](../tools/PROFILING.md).
