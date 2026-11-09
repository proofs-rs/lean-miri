#!/usr/bin/env bash
# Finite parity/rollback tests for indexed preparation and imported allocations.
# Build prerequisites first; generated inputs and caller logs belong in scratch/.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build +Miri:olean +MiriTests:olean +Miri.OperationalSafety:olean +Miri.Frontend.ImportMIR:olean +Miri.Input.ExecutionChoicePolicy:olean +NativeRunner:olean typed_function_abi_tests
python3 tests/input/build_id_fixtures.py
# Performance readers need genuine successful exports, independently of the
# synthetic ID cases. Regenerate them with the current pinned producer.
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-${CARGO_HOME:-$PWD/.cargo}}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-${RUSTUP_HOME:-$PWD/.rustup}}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$PWD/scratch/miri-sysroot}"
export PATH="$CARGO_HOME/bin:$PATH"
performance_toolchain=miri-exporter-8144389c895d
performance_sysroot="$(rustup run "$performance_toolchain" rustc --print sysroot)"
export PATH="$performance_sysroot/bin:$PATH"
export LD_LIBRARY_PATH="$performance_sysroot/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cargo +"$performance_toolchain" build --locked --offline --manifest-path exporter/Cargo.toml
exporter/target/debug/lean-miri-mir-exporter \
  --output scratch/decoder-id-inputs/genuine-mir-features.json exporter/fixtures/mir_features.rs \
  --crate-type=lib --crate-name=mir_features
# The tracked helper supplies real caller-location constants for indexed lookup.
exporter/target/debug/lean-miri-mir-exporter \
  --output scratch/decoder-id-inputs/genuine-fresh.json --root root -- \
  exporter/fixtures/source126_compact.rs --crate-type=lib --crate-name=performance_caller \
  -Cpanic=abort --edition=2021 -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" \
  --cfg=miri -Zalways-encode-mir
for test in DefinitionLookup2026 DecoderProfile2026 PreparationProfile2026 RuntimeStartupProfileIdentity2026 FinalizationProfileIdentity2026 CompilerForeignSymbolTables; do
  lake env lean "MiriTests/Input/$test.lean"
done
for test in SpanPool AllocationImageIndexed2026; do
  lake env lean --run "MiriTests/Input/$test.lean"
done
for test in DecoderDynamicScan2026 CompilerBacktraceIndexTests2026 TypedCompilerPreparationTests; do
  lake env lean --run "tests/input/$test.lean" scratch/decoder-id-inputs/genuine-mir-features.json
done
lake env lean --run tests/constant/AllocationImageTests.lean scratch/decoder-id-inputs/genuine-mir-features.json
for test in AllocatorIds MemoryState GlobalMutationPrefixes; do
  lake env lean --run "MiriTests/MemoryState/$test.lean"
done
lake env lean MiriTests/AxiomAudit.lean

lake env lean --run tests/input/CallerLocationIndex2026.lean scratch/decoder-id-inputs/genuine-fresh.json
.lake/build/bin/typed_function_abi_tests scratch/decoder-id-inputs/genuine-mir-features.json
