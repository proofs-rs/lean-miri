#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-instance-caller-location.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${CALLER_QUERY_OUT:-$ROOT/scratch/caller-location-queries}"
mkdir -p "$OUT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
CARGO_TARGET_DIR="$BASELINE/exporter/target" bash "$BASELINE/tools/export-mir.sh" \
  --output "$OUT/baseline.json" --root caller_attributes -- \
  "$ROOT/tests/repro/compiler-queries/caller-attributes.rs" --crate-type=lib --crate-name=caller_attributes
bash "$ROOT/tools/export-mir.sh" --output "$OUT/candidate.json" \
  --root caller_attributes -- "$ROOT/tests/repro/compiler-queries/caller-attributes.rs" \
  --crate-type=lib --crate-name=caller_attributes
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.TableTail Miri.Input.CompilerRuntimeQueries
lake env lean --run tools/CompareInstanceCallerLocation.lean "$OUT/baseline.json" "$OUT/candidate.json"
