#!/usr/bin/env bash
# Finite parity/rollback tests for indexed preparation and imported allocations.
# Build prerequisites first; generated inputs and caller logs belong in scratch/.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build +Miri:olean +MiriTests:olean +Miri.OperationalSafety:olean +Miri.Frontend.ImportMIR:olean +Miri.Input.ExecutionChoicePolicy:olean +NativeRunner:olean source_abi_boundary_tests
python3 tests/input/build_id_fixtures.py
# Performance readers need genuine successful exports, independently of the
# synthetic ID cases. Regenerate them with the current pinned producer.
export CARGO_HOME="${LEAN_MIRI_CARGO_HOME:-${CARGO_HOME:-$PWD/.cargo}}"
export RUSTUP_HOME="${LEAN_MIRI_RUSTUP_HOME:-${RUSTUP_HOME:-$PWD/.rustup}}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$PWD/scratch/miri-sysroot}"
export PATH="$CARGO_HOME/bin:$PATH"
performance_toolchain=miri-exporter-8eb778d04094
performance_sysroot="$(rustup run "$performance_toolchain" rustc --print sysroot)"
export PATH="$performance_sysroot/bin:$PATH"
export LD_LIBRARY_PATH="$performance_sysroot/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
rustup run "$performance_toolchain" cargo build --locked --offline --manifest-path exporter/Cargo.toml
exporter/target/debug/lean-miri-mir-exporter \
  --output scratch/decoder-id-inputs/genuine-mir-features.json --root direct_tag_value --root get_vtable_root --root as_trait_object --root as_drop_trait_object --root call_trait_object --root make_link --root promoted_ref --root byte_string --root pointer_slice --root get_static_ptr --root read_tls --root id --root array_len --root exercise exporter/fixtures/mir_features.rs \
  --crate-type=lib --crate-name=mir_features
# Retain exact type-name catalog controls alongside indexed preparation checks.
exporter/target/debug/lean-miri-mir-exporter \
  --output scratch/decoder-id-inputs/genuine-fresh.json --root root -- \
  tests/fixtures/caller_location/type_name.rs --crate-type=lib --crate-name=performance_type_name \
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

lake env lean --run tests/input/TypeNameConstants2026.lean scratch/decoder-id-inputs/genuine-fresh.json
.lake/build/bin/source_abi_boundary_tests scratch/decoder-id-inputs/genuine-mir-features.json
