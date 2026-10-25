#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
# Fixture exports use the same pinned Miri std metadata as reference runs.
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
TOOLCHAIN="miri-exporter-8144389c895d"
SYSROOT="$("$CARGO_HOME/bin/rustup" run "$TOOLCHAIN" rustc --print sysroot)"
export PATH="$ROOT/.elan/bin:$SYSROOT/bin:$CARGO_HOME/bin:$PATH"
export LD_LIBRARY_PATH="$SYSROOT/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

"$CARGO_HOME/bin/cargo" +"$TOOLCHAIN" build --offline --manifest-path "$ROOT/exporter/Cargo.toml"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build Miri.Input
lake env lean "$ROOT/MiriTests/Input/CompilerForeignSymbolTables.lean"
lake env lean "$ROOT/MiriTests/Input/DefinitionLookup2026.lean"
lake env lean "$ROOT/MiriTests/Input/DecoderProfile2026.lean"
lake env lean "$ROOT/MiriTests/Input/PreparationProfile2026.lean"
lake env lean "$ROOT/MiriTests/Input/RuntimeStartupProfileIdentity2026.lean"
lake env lean --run "$ROOT/MiriTests/Input/CompilerSpanInterner2026.lean"
lake env lean --run "$ROOT/MiriTests/Input/AllocationImageIndexed2026.lean"

OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-XXXXXX.json")"
SCOPE_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-scope-XXXXXX.json")"
LOWERING_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-lowering-XXXXXX.json")"
NOOP_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-noop-XXXXXX.json")"
ALLOC_WORLD_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-alloc-world-XXXXXX.json")"
ROOT_WORLD_OUT="$(mktemp "${TMPDIR:-/tmp}/lean-miri-input-root-world-XXXXXX.json")"
trap 'rm -f "$OUT" "$SCOPE_OUT" "$NOOP_OUT" "$LOWERING_OUT" "$ALLOC_WORLD_OUT" "$ROOT_WORLD_OUT"' EXIT
"$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$OUT" "$ROOT/exporter/fixtures/mir_features.rs" \
  --crate-type=lib --crate-name=mir_features
python3 "$ROOT/exporter/tests/validate_fixture.py" "$OUT"
lake env lean --run "$ROOT/tests/input/SharedGraphTests.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/RuntimeDecodeEquivalence165.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/DecoderTests.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/SharedGraphDecoderTests.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/DecoderDynamicScan2026.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/SharedFunctionAbiTests.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/CompilerFunctionAbiMemoTests2026.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/CompilerBacktraceIndexTests2026.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/CompilerPreparationInterner2026.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/ImportCLI.lean" "$OUT"
lake env lean --run "$ROOT/tests/input/LowerProgramTests.lean" "$OUT"

"$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$SCOPE_OUT" --root add_one "$ROOT/exporter/fixtures/scope/simple.rs" \
  --crate-type=lib --crate-name=scoped_closure
python3 "$ROOT/exporter/tests/validate_scope_fixture.py" "$SCOPE_OUT"
lake env lean --run "$ROOT/tests/input/SharedGraphTests.lean" "$SCOPE_OUT"
lake env lean --run "$ROOT/tests/input/RuntimeDecodeEquivalence165.lean" "$SCOPE_OUT"
lake env lean --run "$ROOT/tests/input/SelectedScopeTests.lean" "$SCOPE_OUT"
lake env lean --run "$ROOT/tests/input/LowerMIRTests.lean" "$SCOPE_OUT"
lake env lean --run "$ROOT/tests/input/LowerMIRConstructorsTests.lean" "$OUT"

"$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$NOOP_OUT" --root covered "$ROOT/exporter/fixtures/mir_noops.rs" \
  --crate-type=lib --crate-name=mir_noops -Cinstrument-coverage -Zno-profiler-runtime
python3 "$ROOT/exporter/tests/validate_noops_fixture.py" "$NOOP_OUT"
lake env lean --run "$ROOT/tests/input/NoopTests.lean" "$NOOP_OUT"

"$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$LOWERING_OUT" "$ROOT/exporter/fixtures/mir_lowering.rs" \
  --crate-type=lib --crate-name=mir_lowering
lake env lean --run "$ROOT/tests/input/LowerProgramTests.lean" "$LOWERING_OUT"

# A genuine function-pointer + trait-object fixture exercises selected
# allocator-key witnesses. The small root_u32 export covers the same prepared
# raw-ID prefix through execution input.
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 "$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$ALLOC_WORLD_OUT" --root root -- \
  "$ROOT/tests/fixtures/selected_alloc_keys.rs" \
  --crate-type=lib --crate-name=selected_alloc_keys -Cpanic=abort --edition=2021 \
  -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir
python3 "$ROOT/exporter/tests/validate_selected_alloc_world157.py" "$ALLOC_WORLD_OUT"
lake env lean --run "$ROOT/tests/input/SelectedAllocIdCatalog157.lean" "$ALLOC_WORLD_OUT" selected
lake env lean --run "$ROOT/tests/input/AllocWorldRuntime161.lean" "$ALLOC_WORLD_OUT"

LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 "$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$ROOT_WORLD_OUT" --root root_u32 -- \
  "$ROOT/tests/eval_core/fixtures/root_u32.rs" \
  --crate-type=lib --crate-name=root_u32 -Cpanic=abort --edition=2021 \
  -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir
lake env lean --run "$ROOT/tests/input/SelectedAllocIdCatalog157.lean" "$ROOT_WORLD_OUT" root

# A genuine direct TypeId intrinsic call and static reference exercise the
# selected, non-exhaustive static and TypeId allocator-world catalog.
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 "$ROOT/exporter/target/debug/lean-miri-mir-exporter" \
  --output "$ALLOC_WORLD_OUT" --root root -- \
  "$ROOT/tests/fixtures/selected_static_typeid.rs" \
  --crate-type=lib --crate-name=selected_static_typeid -Cpanic=abort --edition=2021 \
  -Zmir-opt-level=0 --sysroot "$MIRI_SYSROOT" --cfg=miri -Zalways-encode-mir
python3 "$ROOT/exporter/tests/validate_selected_static_typeid162.py" "$ALLOC_WORLD_OUT"
lake env lean --run "$ROOT/tests/input/SelectedStaticTypeIdRuntime162.lean" "$ALLOC_WORLD_OUT"
