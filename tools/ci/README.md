# Miri regression CI

`.github/workflows/miri-regression.yml` runs only on `main` pushes.
Main runs are not cancelled by later pushes. The matrix
does not fail fast: a failure in one lane does not cancel the other lanes.
All lanes use independent Linux x86_64 `ubuntu-24.04` runners. The public runner's
16 GB RAM is needed by the existing connected replay guards (up to 15.5 GB).
Checks within a lane run sequentially and never share writable Lake artifacts
with another runner.

## Maintained coverage

| Lane | Checks |
| --- | --- |
| `regression` | Two fixture hash manifests and `check.sh`: source/fixture integrity, Python tools, source-analyzer Rust tests, Lean proofs/assertions/axioms, source-extracted component comparisons, the exporter's current Cargo test entry point, fresh input/frontend/runtime-metadata and arithmetic/call/global execution comparisons. |
| `extended` | Build prerequisites; decoder, structural, optimization and connected-proof scripts; intrinsic float/AES/random-memory comparisons; scheduler and SC prefixes; detached join ordering; source-extracted selector; fresh primitive-range producer/Lean decoder contract; native math ABI. Then a separate reference-feature release exporter for fresh powi-zero, math capability, timezone and three vtable identity controls. |
| `replay` | Build prerequisites, all canonical12 saved exports, four ordering controls, large Tree Borrows and SC diagnostic seeds 0–11 with negative-log checks. |

`check.sh` owns the common `miri_tests` runtime registry and axiom audit. Other
lanes build their own prerequisites without rerunning that registry. Their
specialized scripts retain their own assertions and audits. The workflow requires
all three lanes to pass, so this removes duplicate runs without dropping checks.
Similarly, quick/full audit and Python checks run once through `check.sh`; the
two hash manifests unique to `check-quick.sh` remain separate suites. Replay needs
no Rust/reference build and therefore skips the SDK disk cleanup step.

`python3 tools/ci/run.py LANE --list` prints the exact commands. The runner invokes
existing assertions and comparisons without changing their expected outcomes.
Each top-level suite has a timeout. A nonzero exit, missing executable, or timeout
fails the lane; later suites are still attempted. Some existing scripts stop at
their first failure internally, so a failed suite does not mean its later cases
ran. No unavailable toolchain is silently skipped. Failed prerequisite suites
can cause subsequent suites to fail as well; inspect the first setup/build error.

Saved replay checks stored, hash-matched Miri observations; it does not freshly
invoke reference Miri. Fresh checks build the pinned Miri reference and matching
MIR-enabled standard library, then compare new exports/guest outcomes. Vtable
controls explicitly expect identity, not a nonidentity witness. Native math's
capability check deliberately distinguishes expected Unsupported from success.
These are finite regressions against repository-pinned source, not a general
equivalence proof or a comparison with the latest upstream Miri. See
`STATUS.md` for remaining validation gaps and `tests/README.md` for individual
test contracts.

## Setup and local reproduction

On a fresh Linux x86_64 checkout with Python 3.12, curl, bash, util-linux/flock,
a C/C++ compiler, make, ripgrep (`rg`) and normal Rust build dependencies available:

```bash
bash tools/ci/setup.sh regression
export ELAN_HOME="$PWD/.elan" CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export MIRI_SYSROOT="$PWD/scratch/miri-sysroot" LEAN_NUM_THREADS=1
export PATH="$ELAN_HOME/bin:$CARGO_HOME/bin:$PATH"
python3 tools/ci/run.py regression
```

Replace the lane for the other commands. `replay` setup only installs Lean;
the other lanes also install repository-local stable Rust, install and verify
the exact pinned rustc-dev compiler, prefetch locked Cargo dependencies, and run
the existing reference Miri/sysroot setup. Setup needs network access. Fresh
checks deliberately require new output paths: use a fresh checkout or move
previous `scratch/ci-fresh` output before repeating the extended lane. Setup
does not delete previous evidence. Non-replay setup checks for ripgrep before
installing toolchains; the workflow installs Ubuntu's `ripgrep` package explicitly.
Several source-comparison shell drivers invoke `rg`, so it is a test prerequisite,
not an optional convenience.

## Logs and timing

Each lane uploads `scratch/ci` and selected diagnostic logs even on failure.
`results.json` includes the checked commit, Lean/Rust/Miri pins, exact commands,
exit statuses, per-suite wall seconds and timeout budgets. It is updated after
each suite; `complete: false` indicates an interrupted run. The GitHub step
summary shows a suite table after completion. Setup has its own `/usr/bin/time`
record and machine/toolchain details in `environment.txt`.

This first CI uses fresh builds without restored toolchain, Cargo or Lake caches,
so cache state is consistent across runs. Suite timings include the builds and
fixture generation performed by their existing scripts; `setup.log` measures
installation/reference preparation separately. Timings on shared runners are
diagnostic, not a controlled interpreter benchmark. No speed threshold determines
correctness. Use `tools/PROFILING.md` for performance claims.

The connected-libc build records Cargo's reported archive in
`scratch/connected-libc-target/libc-rlib.path`. Timezone consumes that exact path;
missing or ambiguous artifacts and stale records after a failed rebuild fail.
