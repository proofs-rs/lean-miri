#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/source-mir.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" build \
  Miri.Frontend.FoundationEntrySeed Miri.Input.SourceCompilerBodies
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation --root main --root start -- \
  tests/foundation/fixtures/compiler-entry.rs --crate-name source_mir_custom -Cpanic=abort
bash tools/export-mir.sh --output "$TASK_DIR/reference.json" --root main -- \
  tests/foundation/fixtures/compiler-entry.rs --crate-name source_mir_custom -Cpanic=abort
for test in FoundationSourceMir SourceMirWorld; do
  env ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
    "tests/foundation/$test.lean" "$TASK_DIR/source.json"
done
env ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/SourceMirOracle.lean "$TASK_DIR/source.json" "$TASK_DIR/reference.json"
