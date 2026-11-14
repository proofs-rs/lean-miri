#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-needs-drop.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${NEEDS_DROP_OUT:-$ROOT/scratch/needs-drop}"
mkdir -p "$OUT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/$version.json" --root needs_drop_types -- \
    "$ROOT/tests/repro/compiler-queries/needs-drop.rs" \
    --crate-type=lib --crate-name=needs_drop_types
done
cd "$ROOT"
if [[ "${NEEDS_DROP_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.StructuralNeedsDrop Miri.Input.TableTail
fi
lake env lean tests/compiler_queries/StructuralNeedsDrop.lean
lake env lean --run tools/CompareNeedsDrop.lean "$OUT/baseline.json" "$OUT/candidate.json"
python3 - "$OUT" <<'PY'
import copy
import json
from pathlib import Path
import sys
out = Path(sys.argv[1])
candidate = json.loads((out / 'candidate.json').read_text())
selected = next(index for index, definition in enumerate(candidate['definitions']) if 'adt_drop' in definition)
missing = copy.deepcopy(candidate)
missing['definitions'][selected].pop('adt_drop')
(out / 'missing-material.json').write_text(json.dumps(missing))
invalid = copy.deepcopy(candidate)
invalid['definitions'][selected]['adt_drop']['destructor'] = len(candidate['definitions'])
(out / 'invalid-destructor.json').write_text(json.dumps(invalid))
PY
for kind in missing-material invalid-destructor; do
  if lake env lean --run tools/CompareNeedsDrop.lean "$OUT/baseline.json" "$OUT/$kind.json" >"$OUT/$kind.log" 2>&1; then
    echo "malformed needs_drop material was accepted: $kind" >&2
    exit 1
  fi
done
rg -q 'candidate raw ADT drop material absent' "$OUT/missing-material.log"
rg -q 'candidate destructor identity out of bounds' "$OUT/invalid-destructor.log"
echo "PASS needs_drop missing-material and invalid-destructor negative controls"

# Bounded real-Rust export of a shared ADT DAG. The borrowed argument avoids
# allocating its exponentially large value; material graph size is linear.
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  timeout "${NEEDS_DROP_DAG_TIMEOUT:-90}" env CARGO_TARGET_DIR="$checkout/exporter/target" \
    bash "$checkout/tools/export-mir.sh" --output "$OUT/dag-$version.json" \
    --root needs_drop_dag -- "$ROOT/tests/repro/compiler-queries/needs-drop-dag.rs" \
    --crate-type=lib --crate-name=needs_drop_dag
done
lake env lean --run tools/CompareNeedsDrop.lean "$OUT/dag-baseline.json" "$OUT/dag-candidate.json" --no-drop-dag
