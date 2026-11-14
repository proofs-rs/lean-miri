#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-struct-layout-wrapper.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${STRUCT_LAYOUT_OUT:-$ROOT/scratch/struct-layout-wrapper}"
mkdir -p "$OUT"
cd "$ROOT"
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/baseline.json" \
  --root struct_layouts -- tests/compiler_queries/struct-layouts.rs \
  --crate-type=lib --crate-name=struct_layouts
flock /tmp/lean-miri-lake-build.lock lake build Miri.ABI.StructLayout Miri.Input.Decoder
lake env lean --run tests/compiler_queries/StructLayouts.lean "$OUT/baseline.json"
