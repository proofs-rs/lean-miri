#!/usr/bin/env bash
# Component correspondence checks; this does not establish a whole-compiler port.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-material-queries.sh CANONICAL_BASELINE_CHECKOUT}"
cd "$ROOT"
OUT="${MATERIAL_QUERY_OUT:-$ROOT/scratch/material-query-checks}"
mkdir -p "$OUT"
flock /tmp/lean-miri-lake-build.lock lake build \
  Miri.Input.CompilerFacts Miri.Input.CompilerRuntimeQueries \
  Miri.Input.CallResolution Miri.Input.Decoder \
  MiriTests.Input.StructuralDeref MiriTests.Input.StructuralTail \
  MiriTests.Input.GenericRebase
for source in TypeConstructors TypeArena Normalization StructuralAutoTraits StructuralNeedsDrop StructuralSized InstanceCallerLocation; do
  lake env lean "tests/compiler_queries/$source.lean"
done
bash tests/abi/run_initial_arg_abi.sh
bash tests/abi/run_unwind_seed.sh
bash tools/check-structural-type-queries.sh "$BASELINE"
lake env lean --run tools/ComparePointerMetadata.lean \
  "${STRUCTURAL_QUERY_OUT:-$ROOT/scratch/structural-type-queries}/baseline.json"
bash tools/check-generic-rebase.sh "$BASELINE"
bash tools/check-needs-drop.sh "$BASELINE"
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" \
    bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/primitive-$version.json" --root primitive_layouts -- \
    "$ROOT/tests/compiler_queries/primitive-layouts.rs" \
    --crate-type=lib --crate-name=primitive_layouts
done
lake env lean --run tests/compiler_queries/PrimitiveLayouts.lean \
  "$OUT/primitive-baseline.json" "$OUT/primitive-candidate.json"
lake env lean --run tests/compiler_queries/TypeArenaRuntime.lean \
  "$OUT/primitive-candidate.json"
lake env lean --run tests/compiler_queries/LazyPointerLayouts.lean \
  "${STRUCTURAL_QUERY_OUT:-$ROOT/scratch/structural-type-queries}/baseline.json" \
  "$OUT/primitive-candidate.json"
echo "Compiler material component checks passed (finite comparisons only)."
