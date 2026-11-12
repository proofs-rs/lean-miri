#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-structural-type-queries.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${STRUCTURAL_QUERY_OUT:-$ROOT/scratch/structural-type-queries}"
mkdir -p "$OUT"
# Baseline must be separately built at the PR's canonical base. Its rows are an
# independent rustc oracle and are never consumed by production query providers.
RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}" \
CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}" \
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}" \
bash "$BASELINE/tools/export-mir.sh" --output "$OUT/baseline.json" \
  --root structural_types -- "$ROOT/tests/repro/compiler-queries/structural-types.rs" \
  --crate-type=lib --crate-name=structural_types
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.TableCore Miri.Input.StructuralDeref Miri.Input.StructuralTail Miri.Input.StructuralAutoTraits
lake env lean --run tools/CompareStructuralTypeQueries.lean "$OUT/baseline.json"
