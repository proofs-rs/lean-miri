#!/usr/bin/env bash
# New path consumes declarations; schema12 is an independent compiler oracle.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
TASK_DIR="$(mktemp -d "$ROOT/scratch/fn-vtable.XXXXXX")"
trap 'rm -rf "$TASK_DIR"' EXIT
flock /tmp/lean-miri-lake-build.lock env ELAN_HOME="$ROOT/.elan" \
  "$ROOT/.elan/bin/lake" build Miri.Frontend.FoundationFnVtable
bash tools/export-mir.sh --output "$TASK_DIR/source.json" --foundation --root boundary -- \
  exporter/fixtures/foundation_fn_vtable.rs --crate-name fn_vtable
bash tools/export-mir.sh --output "$TASK_DIR/compiler.json" --root concrete_vtable -- \
  exporter/fixtures/foundation_fn_vtable.rs --crate-name fn_vtable
ELAN_HOME="$ROOT/.elan" "$ROOT/.elan/bin/lake" env lean --run \
  tests/foundation/FoundationFnVtable.lean "$TASK_DIR/source.json" "$TASK_DIR/compiler.json"
bash tools/export-mir.sh --output "$TASK_DIR/identity.json" --foundation --root identity -- \
  exporter/fixtures/foundation.rs --crate-type=lib --crate-name foundation
python3 - "$TASK_DIR/source.json" "$TASK_DIR/identity.json" <<'PY'
import json, sys
source, identity = [json.load(open(path)) for path in sys.argv[1:]]
assert source['fn_vtable_source'] is not None
assert identity['fn_vtable_source'] is None
assert not any(key.startswith('compiler_') for key in source)
assert not any(key.startswith('compiler_') for key in identity)
PY
if bash tools/export-mir.sh --output "$TASK_DIR/unavailable.json" --foundation --root concrete_vtable -- \
    exporter/fixtures/foundation_fn_vtable.rs --crate-name fn_vtable >"$TASK_DIR/unavailable.log" 2>&1; then
  echo 'unsupported promoted concrete vtable source unexpectedly exported' >&2
  exit 1
fi
rg -q 'foundation: unsupported promoted bodies: 1' "$TASK_DIR/unavailable.log"
