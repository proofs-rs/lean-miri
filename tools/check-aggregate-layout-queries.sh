#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-aggregate-layout-queries.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${AGGREGATE_LAYOUT_OUT:-$ROOT/scratch/aggregate-layout-queries}"
mkdir -p "$OUT"
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.ABI.UnivariantLayout Miri.Input.Decoder
for seed in default 0 42 18446744073709551615; do
  FLAGS=()
  if [[ "$seed" != default ]]; then
    FLAGS=(-Zrandomize-layout "-Zlayout-seed=$seed")
  fi
  CARGO_TARGET_DIR="$BASELINE/exporter/target" \
    bash tools/export-mir.sh --output "$OUT/baseline-$seed.json" \
    --root aggregate_layouts -- tests/compiler_queries/aggregate-layouts.rs \
    --crate-type=lib --crate-name=aggregate_layouts "${FLAGS[@]}"
  lake env lean --run tests/compiler_queries/AggregateLayouts.lean "$OUT/baseline-$seed.json"
done
