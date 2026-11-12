#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-generic-rebase.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${GENERIC_REBASE_OUT:-$ROOT/scratch/generic-rebase}"
mkdir -p "$OUT"
RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}" \
CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}" \
CARGO_TARGET_DIR="$BASELINE/exporter/target" \
MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}" \
bash "$BASELINE/tools/export-mir.sh" --output "$OUT/baseline.json" \
  --root generic_rebase -- "$ROOT/tests/repro/compiler-queries/generic-rebase.rs" \
  --crate-type=lib --crate-name=generic_rebase
python3 - "$OUT/baseline.json" "$OUT/oracle.json" <<'PY'
import json
import sys

with open(sys.argv[1]) as source:
    document = json.load(source)
instances = {row['instance_id']: row for row in document['instances']}
rows = []
for row in document['compiler_runtime_queries']['virtual']:
    rows.append({'args': instances[row['original_instance_id']]['generic_args'],
                 'concrete_type': row['concrete_type'],
                 'rebased_args': row['rebased_args']})
if not rows:
    raise SystemExit('no real virtual rebase oracle rows')
with open(sys.argv[2], 'w') as target:
    json.dump(rows, target)
PY
cd "$ROOT"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.GenericRebase Miri.Input.GenericArgsCodec
lake env lean --run tools/CompareGenericRebase.lean "$OUT/oracle.json"
