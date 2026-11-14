#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-union-layout-queries.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${UNION_LAYOUT_OUT:-$ROOT/scratch/union-layout-queries}"
mkdir -p "$OUT"
cd "$ROOT"
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/baseline.json" \
  --root union_layouts -- tests/compiler_queries/union-layouts.rs \
  --crate-type=lib --crate-name=union_layouts
flock /tmp/lean-miri-lake-build.lock lake build Miri.ABI.UnionLayout Miri.Input.Decoder
CARGO_TARGET_DIR="$ROOT/exporter/target"   bash tools/export-mir.sh --output "$OUT/candidate.json"   --root union_layouts -- tests/compiler_queries/union-layouts.rs   --crate-type=lib --crate-name=union_layouts
lake env lean --run tests/compiler_queries/UnionLayouts.lean   "$OUT/baseline.json" "$OUT/candidate.json"
