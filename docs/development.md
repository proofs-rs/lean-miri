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
