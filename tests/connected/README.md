# Connected finite checks and component proofs

Self-contained component proofs live in [MiriTests/Connected/Proofs](../../MiriTests/Connected/Proofs/)
and are built by `lake build MiriTests`. Input-dependent graph exploration stays
in `tests/connected/proofs/`; the proof checker only typechecks that graph runner.

Run after setup in the root README and `bash tools/check-build.sh`.
The authoritative inputs and assertions are [cases.py](cases.py), the adjacent
Lean harnesses and Rust sources in fixtures. Remaining work is managed only in
[STATUS](../../STATUS.md).

```bash
python3 tools/check-connected.py --case 198-sc-base
python3 tools/check-connected.py             # canonical12
python3 tools/check-connected.py --ordering  # 4 controls
python3 tools/check-connected.py --large-tb  # Expected TB UB
python3 tools/check-sc-schedules.py         # Finite sample of fixed seeds 0–11
bash tools/check-connected-proofs.sh
python3 tests/connected/compare_selector.py
bash tools/check-structural-regressions.sh  # Additional typechecking, kernel examples and #eval
```

canonical12 covers normal exit after protector release / active-protector UB,
RMW release / a race after replacement with a store, custom DST, normal / negative
TLS-drain prefixes, main constructor order, dyn upcasts A/B and
SC / Relaxed(0,0). Reference inputs comprise 9 normal + 3 expected UB cases.
Even for expected UB, the harness itself exits 0 when its assertions hold.
Unsupported, failure and fuel exhaustion cannot replace expected UB.
The large TB case checks the final write to a Frozen tag after a parent read.

Saved gzip files contain the exact bytes of genuine compiler exports. They are
retained as fixed test inputs depending on raw IDs, prepared query order and
same-TyCtxt references. The schema133 eval_core fixture is a unit input with
separate transport conversion, not a genuine schema3 export.
`SHA256SUMS` and sidecar length/FNV check integrity. Old absolute paths in sidecars
and snapshots are provenance strings from reference generation; execution does
not read files at those locations. Each Rust input is adjacent with the same
basename. Negative-case `.miri-error.txt` files are expected-result fixtures
containing only the UB diagnostic from the original same-TyCtxt reference, not
build/run logs. Do not rewrite fixtures to fit the current implementation.

SC controls select the oldest candidate on the weaker side to demonstrate (0,0)
and check that the corresponding SC side restricts candidates. They also check
every request/input/domain in the typed prefix. The weak fence reference uses
seed2/preemption_rate0; other references use the profile recorded in the sidecar.
These are finite support witnesses, not mutant tests or proofs for all schedules.
`validate_ordering_pairs.py` also compares operation/scheduler order.
Seed checks use `validate_schedule.py` to observe actual atomic-intrinsic
boundaries and reject 3 negative logs: truncation, out-of-support input and missing
post-step records. On the no-choice `.ready` read path, they do not require an
atomicStale choice; they check for 0 or 1 within the actual step interval.
These checks do not freshly execute and compare a Miri reference for each seed.

Proof scripts kernel-check strict-wrapper history erasure/locality, the SC
selector, join, 6 events and exact equality; the graph runner is typechecked.
`compare_selector.py` extracts fetch_store from pinned Rust and compares with a
finite reference replacing the RNG tail with enumeration of all candidates.
It does not execute the Miri interpreter. Proof `.olean` files are generated in scratch.

The retained graph runner also checks fast exact-state equality: self and rebuilt
states compare equal, while changed choice counters, shared nodes and raw source
documents do not. Packed timestamps with equal time but distinct retag bits must
remain unequal. Run those assertions with a one-node graph budget after the
proof script has built its imports:

```bash
mkdir -p scratch/connected-graph
gzip -dc tests/connected/fixtures/198-sc-base.json.gz > scratch/connected-graph/sc.json
LEAN_PATH="$PWD/scratch/connected-proofs:$(.elan/bin/lake env printenv LEAN_PATH)" \
  .elan/bin/lake env lean --run tests/connected/proofs/ConnectedGraph215Schema3.lean \
  scratch/connected-graph/sc.json 1
```

This bounded run checks the equality assertions before exploring one node. Its
OPEN frontier does not establish graph completion, normal guest termination or
whole-machine safety. Canonical SC execution remains covered by `198-sc-base`.

## Fresh exports and reproduction inputs

Saved-fixture replay and fresh export are separate operations. Fresh generation
requires the pinned Miri sysroot and an exporter with the miri-reference feature.

```bash
CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup" \
  .cargo/bin/cargo +miri-exporter-8144389c895d build --locked \
  --manifest-path exporter/Cargo.toml --features miri-reference
# Also build actual libc types and MIR metadata for pthread cases with the same sysroot
CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup" \
  .cargo/bin/cargo +miri-exporter-8144389c895d fetch --locked --manifest-path tests/connected/libc/Cargo.toml
bash tools/build-connected-libc.sh
python3 tools/export-connected.py 198-sc-base scratch/exports/new-sc.json \
  --libc scratch/connected-libc-target/x86_64-unknown-linux-gnu/debug/deps/liblibc-HASH.rlib
ELAN_HOME="$PWD/.elan" .elan/bin/lake env lean --run \
  tests/connected/198-sc-base.lean scratch/exports/new-sc.json
```

Replace `HASH` with the actual filename produced by the build. Case roots and
compiler arguments are expanded from cases.py. If a new allocation history
changes expectations such as fixed cursors, preserve and investigate the failure
rather than automatically updating expectations. For negative cases, inspect the
reference Miri error in the sidecar and original UB diagnostic; a nonzero export
process alone is not evidence of expected UB.

Supplemental Rust inputs are in [repro/](../repro/) and additional harnesses in
[focused/](focused/). Keep them separate from canonical12 fixtures, freshly export
the original Rust with the pinned toolchain, and check the harness's required
root, foreign connections and expected arguments. See STATUS for detailed
current applicability.

To regenerate the same weak-fence reference profile,
`bash tools/build-reference-profile.sh` applies the combined patch in
[reference/](reference/) to an exporter copy in scratch and builds it against
pinned upstream sources. Only that copy uses `LEAN_MIRI_REFERENCE_SEED=2` and
`LEAN_MIRI_REFERENCE_PREEMPTION_RATE=0`. The patch is for reference use and does
not change production semantics. Check the actual profile in the new sidecar;
do not count an unestablished (0,0) as success.

All 4 ordering inputs can use the same export entry point. For example,
regenerate the weak fence reference with:

```bash
bash tools/build-reference-profile.sh
python3 tools/export-connected.py fence-acqrel scratch/exports/new-fence-control.json \
  --libc scratch/connected-libc-target/x86_64-unknown-linux-gnu/debug/deps/liblibc-HASH.rlib \
  --exporter scratch/reference-profile-target/debug/lean-miri-mir-exporter
```

This entry point sets seed2/preemption_rate0 on the reference copy. After
generation, check the sidecar's actual profile and guest outcome. `fence-sc`,
`rmw-sc` and `rmw-relaxed` use the default reference profile. Do not assume a
re-export with new query history will pass an old typed tape; distinguish it
from replay of the retained fixtures.
