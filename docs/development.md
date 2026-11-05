# Development and validation

Run the commands below from the repository root. For the Lean library alone,
use `lake build Miri` as described in the [README](../README.md#build).

## Rust toolchain and reference setup

The main execution and reference checks require Linux x86_64, Python 3, bash,
flock, a C compiler and Rustup/Cargo. Install Rustup/Cargo under `.cargo/bin/`
(for example, install Rustup with `CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"`).
Lean is pinned to `leanprover/lean4:v4.35.0` in `lean-toolchain`, Miri to
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, and rustc to
`8144389c895da997dbdecaa635e41d6a50be6ffd`.
`upstream/.pins/` and the source lock are authoritative. Reading the parent
repository's Git HEAD from an upstream directory does not verify the upstream
version. The pinned rustc sources cover a selected investigation scope, not a
complete audit of the semantic dependency closure.

Run from the repository root. Initial downloads require network access.

```bash
bash tools/setup-lean.sh
bash tools/setup-rustc-exporter.sh
export ELAN_HOME="$PWD/.elan" CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
cargo fetch --locked --manifest-path tools/source-analysis/Cargo.toml
cargo +miri-exporter-8144389c895d fetch --locked --manifest-path exporter/Cargo.toml
```

Fresh comparisons with Miri require a standard library containing MIR from the
same version. Generate it with `bash tools/setup-miri-reference.sh`. Artifacts
are stored in `scratch/` and the ignored upstream `target/` directory. Lean replay
of saved fixtures, decoder checks and local proofs do not require the reference
Miri binary or old working checkouts.

## Exporter construction and wire compatibility

The exporter constructs persistent shared values: cloning a payload retains its
immutable node, and mutation copies only changed containers. Metadata patch
passes memoize construction nodes; final encoding visits each shared source
node once per applicable field role. Structural interning uses exact ordered
wire equality (including numeric spelling), with full equality on hash collisions.
Pointer identity is only a document-local traversal optimization, never a Rust
allocation/type identity or a wire ID. Compiler query evaluation order is unchanged.

The default external format is `lean-miri-prepared-image` version 1. It contains
an interned field-name dictionary and a bottom-up indexed node table. Row tags
are null, false, true, number, string, array-of-node-IDs and
object-of-(field-ID,node-ID)-pairs (tags 0 through 6). Object names are strictly
ordered; every edge points to an earlier row. Node IDs are transport identities,
not Rust allocation, type, instance or MIR indices. The reconstructed business
document still uses MIR schema 3. This is still JSON transport; it does not remove
JSON parsing or precompute unchecked execution/readiness results in Rust.

Canonical immutable construction nodes are interned as they are built, with exact
ordered wire equality on hash collisions. The final encoder visits source nodes
by identity instead of performing another structural deduplication pass. The
output table stays in typed Rust rows through serialization to the writer; it
never becomes another generic JSON Value tree. Weak
pool entries do not own compiler payloads. Mutation invalidates the cached hash
and copies a shared container before changing it.

The prepared allocator world uses `rustc_alloc_id_world_v2`: `raw_kinds` has one
ASCII kind tag per source AllocId, and `opaque_memory` carries memory projections
not already owned by supported allocation nodes. The reader reconstructs the
same complete raw pool and runs the full identity, frontier, salt/key and byte
family checks. This normalizes repeated facts; it does not remove opaque IDs or
change completeness requirements. Legacy `v1` worlds remain accepted. The
`full-allocation-world` exporter feature emits the reference `v1` representation.

Caller-location rows use `caller_location_template_v1`: the compiler produces
one immutable Location template per filename, and each source span retains the
effective u32 line/column, including macro expansion and redaction behavior.
The interpreter constructs a fresh root for each invocation using the compiler's
physical field offsets and checked scalar writes. Filename provenance and all
untouched bytes/initialization are preserved. Literal query APIs reject recipes
rather than expose an uninstantiated template. `full-caller-locations` retains the
fully materialized compiler-query reference producer. These are compilation-local
tables; neither format uses a shared program cache.

`bash tools/check-compact-input.sh` compares genuine reference/normalized exports,
the complete Lean allocation-world results and malformed-world rejection, and
checks immutable construction with both target endiannesses. The performance
regression entry point also runs it. The same check compares every source span
in a macro/track-caller fixture against fully materialized compiler images under
four location-detail settings, including complete redaction.
After building with `bash tools/build-exporter.sh --features miri-reference`,
`python3 tools/check-caller-location-runtime.py --output scratch/caller-location-runtime`
checks real macro/track-caller coordinates and repeated-call allocation identity
against same-prepared-TyCtxt Miri. This is separate from upstream inventory coverage.

Lean validates every typed row, edge and dictionary entry (including unused
rows), then constructs indexed traversal nodes and their local hashes/summaries
in the same pass. The typed MIR reader reuses document-local node IDs and complete
decoding context across MIR roots. Lowering retains its source-consistency check;
a reused result must match both the source path and complete canonical raw value.
Failed decodes fall through to ordinary parsing, preserving diagnostic paths and
first-error order. Only a resolver-produced traversal can populate the opaque
MIR memo. Readiness, compiler evidence and execution checks still run.

Set `LEAN_MIRI_PREPARED_IMAGE=0` to retain shared-payload schema 2 output with the
persistent builder. Lean and `tools/mir_json.py` accept both formats. The
`legacy-json` Cargo feature separately retains the tree builder and string-key
encoder for comparisons. Run exporter Cargo tests normally and with
`--features legacy-json`; add `miri-reference` for reference integration.
`tools/check-decoder.sh` includes typed-row rejection, Python-reader checks and
indexed/legacy parity on retained compiler exports and their malformed ID cases.
Exporter tests also cover forced hash collisions, copy-on-write snapshots,
exact numeric spelling, graph-sized encoding of exponentially repeated input,
and exact/unknown vtable links.

Compiler instance kinds and complete generic arguments are decoded into a shared
import-time source table. Its definition slots are local to each source record;
preparation rebinds them to the current compiler tables and rechecks type
membership. The immutable key includes the complete canonical kind and argument
payloads. Changed contexts, changed fields and failed parses retain the original
decoder/error behavior. Runtime checking also consumes the complete typed
argument projection and rebases its ordered obligations, rather than decoding
that JSON subtree again. Dense node-ID/context buckets accelerate the remaining
runtime walk; raw JSON retains the exact-key map fallback.

Canonical indexed inputs use direct retained-query path lookup for supported
path syntax. Ancestor debug-payload exclusion and canonical index spelling are
preserved; other syntax and uncached inputs use the reference scan. Incremental
span candidates use a persistent hash trie so deferred failures can retain the
old interner without copying its entire index. Complete span equality and first
matching IDs remain decisive.

## What the checks test

See [tests/README.md](../tests/README.md) for the detailed directory map,
`check.sh` inclusion and exclusions, standalone checks and change-based selection.
There is currently no single command that runs every test.

`lake build` checks the default library targets and their theorem declarations.
It does not run every test under `tests/`, and typechecking an interpreter does
not establish that it implements the upstream interpreter correctly.

The additional checks cover three different questions:

- **Lean proofs:** typecheck theorem examples and inspect their axiom dependencies.
- **Behavior:** run executable assertions, reject malformed exported MIR, and compare
  selected component operations and Rust program executions with pinned Miri.
- **Source bookkeeping:** check snapshot hashes, fixture integrity and links from
  reviewed source items to implementations and tests.

`tests/connected/` contains integration tests that run exported Rust programs
through the assembled interpreter. Other test directories mostly exercise
individual components. Both belong to the same test suite.

These checks are development tools; ordinary library users do not need the full
reference toolchain or source audit generator.

## Check commands

The [Miri regression workflow](../.github/workflows/miri-regression.yml) runs the
maintained regression, extended comparison and saved-replay lanes on every
`main` push. See [CI coverage and reproduction](../tools/ci/README.md) for
the exact scope, setup, timing records and retained logs. This workflow uses the
current exporter Cargo test entry point and does not reorganize test ownership.

Self-contained Lean checks have two stages: `lake build MiriTests` and
`lake exe miri_tests`. The latter reruns source assertions regardless of cached
builds; `--list` and `--case MODULE` support focused execution. `check-build.sh`
and `check.sh` run both stages. See the [test guide](../tests/README.md#self-contained-lean-checks-miritests)
for module registration and the boundary with external/input-driven tests.


```bash
mkdir -p scratch/logs
bash tools/check-quick.sh > scratch/logs/quick.log 2>&1
bash tools/check-build.sh > scratch/logs/build.log 2>&1
bash tools/check-decoder.sh > scratch/logs/decoder.log 2>&1
bash tools/check-connected-proofs.sh > scratch/logs/proofs.log 2>&1
```

The quick check validates source pins, audit links, Python tests, semantic lint
and fixed-fixture integrity without building Lean. The build check builds the
Lean library, frontend and all MiriTests modules, including dependencies in a fresh
checkout, runs the self-contained runtime registry, and audits axioms. Proof checks use the kernel and are distinct from
finite comparisons. Rerun finite comparisons for indexing, ABI caching and state
retention with `bash tools/check-performance-regressions.sh`.
Additional structural regressions are checked with
`bash tools/check-structural-regressions.sh` (typechecking, kernel examples,
#eval and executable assertions with pinned unit fixtures or no input). This is
distinct from running supplemental guest harnesses that need fresh exports. The structural
checker prepares pinned adapted schema3 unit fixtures and passes them to
`LowerContext`, `ProviderContext` and `PrimitiveRebinding`, including their runtime
source/cache and error-order assertions. These are not fresh producer comparisons.
`tools/prepare-source-audit.py`
regenerates the AST inventory, dependency candidates and correspondence tables
under `scratch/source-audit/`. Manual review inputs are in `tools/audit/`, and
correspondence-table definitions remain in the existing tools. Inventory status
and correspondence rows classify historical evidence, not current execution results.

Heavy checks can be run separately after building:

```bash
python3 tools/check-connected.py                 # 12 cases; DST and others may take minutes and about 15 GB
python3 tools/check-connected.py --ordering      # 4 SC/weak-ordering controls
python3 tools/check-sc-schedules.py              # Diagnostic seeds 0–11, ordering and negative-log checks
python3 tools/check-connected.py --large-tb      # Frozen-write UB on the same Rust input
bash tools/check.sh                             # Also includes maintained component regressions and fresh export/Miri comparisons
```

Use connected's `--case ID` for individual replay and `--timeout SECONDS` for an
execution limit. Reaching a limit is a failure. The full `check.sh` stops on a
failure, leaving later checks unexecuted. Full checks with fresh exports and
reference executions require the pinned toolchain, Miri sysroot and downloaded
dependency crates. Check fixture assertions and expected output, not just exit
codes. Write generated inputs and logs to ignored `scratch/` or a temporary
directory, and use a new log name for each attempt.

## Source audit tools

`tools/source-analysis/` is a Rust command-line program using `syn` to inspect upstream
Rust syntax. `tools/prepare-source-audit.py` invokes the audit tools to generate
source inventories, dependency candidates and correspondence tables under
`scratch/source-audit/`. Reviewed inputs live in `tools/audit/`. The analyzer is
not used to build or execute the Lean library.

`tools/` contains setup and check commands, Lean executables and Python helpers.

`upstream/source-lock.json` records upstream revisions and content hashes beside
the reference snapshots. Paths inside the lock are relative to the repository
root, including when tools run against the generated audit workspace.

## Interpreting results


The Lean kernel checks theorems about definitions in Lean. MIR generation by
rustc, the exporter's query closure, port fidelity, host implementation and the
relationship between Miri's model and actual Rust are separate trust boundaries.
The permitted logical axioms are `propext`, `Quot.sound` and `Classical.choice`.
Execution tests and source inventories are not general equivalence proofs.

Safety excludes UB on every reachable permitted finite prefix. Distinguish normal
termination, expected UB, Unsupported, fuel exhaustion and execution failure.
Unsupported or unclassified stops do not count as Safe. Fixed-fixture references
are Miri executions in the same prepared TyCtxt after export; they do not promise
the same allocation history as vanilla Miri or agreement for arbitrary seeds.
Client proofs must pin inputs, versions, initial conditions, external contracts,
theorems and axiom dependencies.

## Profiling


Run an execution with profiling enabled:

```bash
bash tools/run.sh scratch/input.json --profile
```

For repeated measurements, use `python3 tools/measure.py --help`.
The collector builds and snapshots the native executable before timing it.
Compare the same input and pinned artifacts on the same CPU with one Lean
thread, using multiple alternating trials. Check the terminal outcome separately:
observing process output does not establish successful execution or safety.

See the [profiling guide](../tools/PROFILING.md) for measurement modes, profiler
boundaries, sampling and interpretation of results.

## Building the API reference

Documentation uses a separate `docbuild` Lake project with doc-gen4 pinned to the
Lean release in `lean-toolchain`. `MiriApi.lean` includes the `Miri` library and the frontend, execution-choice
policy and TLS callback modules outside its import closure;
Rust setup and the comparison fixtures are not required.

After installing the pinned Lean toolchain, run from the repository root:

```bash
(cd docbuild && flock /tmp/lean-miri-lake-build.lock lake build MiriApi:docs)
python3 -m http.server --directory docbuild/.lake/build/doc 8000
```

Open `http://localhost:8000/Miri.html`. Serve the files over HTTP so that search
works. When upgrading Lean, update the doc-gen4 revision in
`docbuild/lakefile.toml` to the matching release and regenerate its manifest with
`(cd docbuild && flock /tmp/lean-miri-lake-build.lock lake update doc-gen4)`.

The `Miri API documentation` workflow builds on pull requests and publishes on
`main` pushes or manual dispatch from `main`. In repository Settings → Pages,
select **GitHub Actions** as the source. The published API entry point is
<https://proofs-rs.github.io/lean-miri/Miri.html>.
