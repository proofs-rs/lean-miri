#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-sequence-layout-queries.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${SEQUENCE_LAYOUT_OUT:-$ROOT/scratch/sequence-layout-queries}"
mkdir -p "$OUT"
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.SequenceLayoutMaterial
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/baseline.json" --root sequence_layouts -- \
  tests/compiler_queries/sequence-layouts.rs --crate-type=lib --crate-name=sequence_layouts
CARGO_TARGET_DIR="$ROOT/exporter/target" \
  bash tools/export-mir.sh --output "$OUT/candidate.json" --root sequence_layouts -- \
  tests/compiler_queries/sequence-layouts.rs --crate-type=lib --crate-name=sequence_layouts
lake env lean --run tests/compiler_queries/SequenceLayouts.lean "$OUT/baseline.json" "$OUT/candidate.json"
lake env lean --run tests/compiler_queries/SequenceLayoutMaterial.lean
