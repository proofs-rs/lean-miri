#!/usr/bin/env bash
# Genuine producer equality plus independent Lean normalization/error checks.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="$PWD/.elan" LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
export PATH="$ELAN_HOME/bin:$PATH"
OUT="$PWD/scratch/compact-input-checks"
mkdir -p "$OUT"
flock --no-fork /tmp/lean-miri-lake-build.lock lake build native_runner
bash tools/build-exporter.sh --features full-allocation-world
cp exporter/target/release/lean-miri-mir-exporter "$OUT/reference-exporter"
EXPORTER_BIN="$OUT/reference-exporter" bash exporter/tests/run-producer.sh selected_alloc_world "$OUT/reference.json"
bash tools/build-exporter.sh
EXPORTER_BIN="$PWD/exporter/target/release/lean-miri-mir-exporter" \
  bash exporter/tests/run-producer.sh selected_alloc_world "$OUT/normalized.json"
python3 exporter/tests/compare_alloc_world.py "$OUT/reference.json" "$OUT/normalized.json"
lake env lean --run tests/input/CompactAllocWorldChecks.lean "$OUT/reference.json"
lake env lean --run tests/allocation/ImmutableTemplateChecks.lean
bash tools/build-exporter.sh --features full-caller-locations
cp exporter/target/release/lean-miri-mir-exporter "$OUT/full-caller-exporter"
bash tools/build-exporter.sh
cp exporter/target/release/lean-miri-mir-exporter "$OUT/recipe-exporter"
export ROOT="$PWD"
source exporter/tests/fixture-env.sh
for details in file,line,column none line,column file; do
  for variant in full-caller recipe; do
    LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 "$OUT/$variant-exporter" \
      --output "$OUT/$variant-$details.json" --root root -- \
      exporter/fixtures/caller_locations.rs --crate-name caller_locations \
      --crate-type lib --edition=2021 -Zmir-opt-level=0 -Zlocation-detail="$details"
  done
  python3 exporter/tests/compare_caller_locations.py \
    "$OUT/full-caller-$details.json" "$OUT/recipe-$details.json"
done
