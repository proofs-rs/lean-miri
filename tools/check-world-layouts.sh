#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-world-layouts.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${WORLD_LAYOUT_OUT:-$ROOT/scratch/world-layouts-check}"
mkdir -p "$OUT"
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.RuntimeMetadata
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/oracle.json" --root world_layout_oracle -- \
  tests/compiler_queries/world-layouts.rs --crate-type=lib --crate-name=world_layouts
CARGO_TARGET_DIR="$ROOT/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/source.json" --root world_layout_material -- \
  tests/compiler_queries/world-layouts.rs --crate-type=lib --crate-name=world_layouts
lake env lean --run tests/compiler_queries/WorldLayouts.lean "$OUT/source.json" "$OUT/oracle.json"
