#!/usr/bin/env bash
# Fresh finite source capture vs schema12's independent foreign-symbol exporter.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/foreign-symbols.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
cat > "$TASK_DIR/input.rs" <<'RS'
#![no_main]
pub fn root(x: u32) -> u32 { x }
RS
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationForeignSymbols
for kind in library binary; do
  crate_flags=()
  if [[ "$kind" == library ]]; then crate_flags=(--crate-type=lib); fi
  bash tools/export-mir.sh --output "$TASK_DIR/$kind-foundation.json" \
    --foundation --root root -- "$TASK_DIR/input.rs" --crate-name foreign_linkage "${crate_flags[@]}"
  bash tools/export-mir.sh --output "$TASK_DIR/$kind-schema12.json" \
    --root root -- "$TASK_DIR/input.rs" --crate-name foreign_linkage "${crate_flags[@]}"
  ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
    tests/foundation/FoundationForeignSymbols.lean \
    "$TASK_DIR/$kind-foundation.json" "$TASK_DIR/$kind-schema12.json"
done
