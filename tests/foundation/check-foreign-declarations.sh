#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/foreign-declarations.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationForeignDeclarations Miri.Input.CompilerSourceSymbols
for mode in custom standard; do
  flags=()
  if [[ "$mode" == custom ]]; then
    source_file=tests/foundation/fixtures/compiler-entry.rs
    count=231
    flags=(-Cpanic=abort)
  else
    source_file=tests/repro/startup/empty-main.rs
    count=244
  fi
  bash tools/export-mir.sh --output "$TASK_DIR/$mode-source.json" --foundation --root main -- \
    "$source_file" --crate-name "$mode" "${flags[@]}"
  bash tools/export-mir.sh --output "$TASK_DIR/$mode-reference-full.json" --root main -- \
    "$source_file" --crate-name "$mode" "${flags[@]}"
  python3 tests/foundation/project_foreign_declarations.py \
    "$TASK_DIR/$mode-reference-full.json" "$TASK_DIR/$mode-reference.json"
  flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
    tests/foundation/FoundationForeignDeclarations.lean "$TASK_DIR/$mode-source.json" "$TASK_DIR/$mode-reference.json" "$count"
done
