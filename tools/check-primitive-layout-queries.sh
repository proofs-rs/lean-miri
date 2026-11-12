#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-primitive-layout-queries.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${PRIMITIVE_LAYOUT_OUT:-$ROOT/scratch/primitive-layout-queries}"
mkdir -p "$OUT"
# Both exporters must already be built with the pinned compiler. This script
# never changes the baseline checkout or adapts production input contracts.
for variant in baseline candidate; do
  if [[ "$variant" == baseline ]]; then
    EXPORT_CHECKOUT="$BASELINE"
  else
    EXPORT_CHECKOUT="$ROOT"
  fi
  CARGO_TARGET_DIR="$EXPORT_CHECKOUT/exporter/target" \
    bash "$ROOT/tools/export-mir.sh" --output "$OUT/$variant.json" \
    --root primitive_layouts -- "$ROOT/tests/compiler_queries/primitive-layouts.rs" \
    --crate-type=lib --crate-name=primitive_layouts
done
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.RuntimeMetadata Miri.Input.Decoder
lake env lean --run tests/compiler_queries/PrimitiveLayouts.lean \
  "$OUT/baseline.json" "$OUT/candidate.json"
