# Supplemental connected harnesses

These retain assertions from focused comparisons beyond the canonical twelve.
For current validation gaps, use [STATUS](../../../STATUS.md).
The no-input collection tests moved to `MiriTests/Connected/Focused/` and are
registered in `lake exe miri_tests`. They are executable independently of guest exports.

| Harness | Rust reproduction | Extra harness argument |
| --- | --- | --- |
| AtomicHandoff.lean | [Acquire](../../repro/atomic-handoff/acquire.rs), [Relaxed](../../repro/atomic-handoff/relaxed.rs) | `expect-zero`, `expect-race` respectively |
| AtomicFence.lean | [positive](../../repro/atomic-fence/positive.rs), [negative](../../repro/atomic-fence/negative.rs) | `expect-zero`, `expect-race` respectively |
| AtomicHandoff.lean | [pthread race with actual libc types](../../repro/race-negative/pthread-race-miri-start.rs) | `expect-race` |
| BacktraceSourceRun.lean | [compact backtrace](../../repro/backtrace/source-e6209e72.rs) | none |
| MiriTests/Connected/Focused/KeyedArray166QA.lean | no Rust input; collision, duplicate and rekey assertions | no arguments |
| MiriTests/Connected/Focused/MemoryState166QA.lean | no Rust input; global, duplicate and raw/dense crosswalk assertions | no arguments |

A fresh guest export requires the pinned toolchain, MIR-enabled Miri sysroot,
reference-feature exporter and the matching libc rlib described in the
[parent instructions](../README.md#fresh-exports-and-reproduction-inputs). From the repository root:

```bash
export CARGO_HOME="$PWD/.cargo" RUSTUP_HOME="$PWD/.rustup"
export MIRI_SYSROOT="$PWD/scratch/miri-sysroot"
toolchain="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export PATH="$toolchain/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
mkdir -p scratch/exports
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 LEAN_MIRI_RUN_PREPARED_MIRI=1 \
  exporter/target/debug/lean-miri-mir-exporter --output scratch/exports/handoff.json \
  --root miri_start -- tests/repro/atomic-handoff/acquire.rs \
  --crate-type=bin --crate-name=handoff --edition=2024 -Cpanic=abort \
  -Zmir-opt-level=0 -Zalways-encode-mir --cfg=miri --sysroot "$MIRI_SYSROOT" \
  --extern libc=scratch/connected-libc-target/x86_64-unknown-linux-gnu/debug/deps/liblibc-HASH.rlib
ELAN_HOME="$PWD/.elan" .elan/bin/lake env lean --run \
  tests/connected/focused/AtomicHandoff.lean scratch/exports/handoff.json expect-zero
```

Replace HASH with the actual built filename. For the other guest rows, substitute
the Rust path, output filename, harness and expected argument from the table.
Inspect the Miri sidecar and exact UB diagnostic for negative cases. A process
failure or Unsupported is not an accepted race witness. A new export changes
compiler query history; do not silently rewrite fixed trace assertions.

The pthread-only race reproduction shares `AtomicHandoff.lean`'s canonical
scheduler/Unix setup. Its `expect-race` mode checks two thread records and the
exact typed `DataRace` error, and rejects exit, Unsupported, failure and pending
outcomes. A separate copy of that runner is unnecessary.
