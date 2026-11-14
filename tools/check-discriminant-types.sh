#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
BASELINE="${1:?usage: check-discriminant-types.sh CANONICAL_BASELINE_CHECKOUT}"
OUT="${DISCRIMINANT_TYPES_OUT:-$ROOT/scratch/discriminant-types}"
mkdir -p "$OUT"
cd "$ROOT"
if [[ "${DISCRIMINANT_TYPES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build \
    Miri.Input.StructuralDiscriminantType Miri.Input.CompilerFacts Miri.Input.Decoder
fi
for version in baseline candidate; do
  checkout="$ROOT"
  if [[ "$version" == baseline ]]; then checkout="$BASELINE"; fi
  CARGO_TARGET_DIR="$checkout/exporter/target" bash "$checkout/tools/export-mir.sh" \
    --output "$OUT/$version.json" --root discriminant_types -- \
    "$ROOT/tests/repro/compiler-queries/discriminant-types.rs" \
    --crate-type=lib --crate-name=discriminant_types_probe
done
python3 - "$OUT" <<'PY'
import json,pathlib,sys
out=pathlib.Path(sys.argv[1]);value=json.loads((out/'baseline.json').read_text())
byte=next(n['type_id'] for n in value['types'] if n['shape']['kind']=='uint' and n['shape']['unsigned_kind']=='u8')
node=next(n for n in value['types'] if n['shape']['kind']=='adt' and n['shape']['adt_kind']=='enum' and n['shape']['representation']['integer'] is None)
node['compiler_facts']['type_queries']['discriminant_type']=byte
(out/'wrong-oracle.json').write_text(json.dumps(value))
PY
lake env lean --run tools/CompareDiscriminantTypes.lean "$OUT/baseline.json" "$OUT/candidate.json"
if lake env lean --run tools/CompareDiscriminantTypes.lean "$OUT/wrong-oracle.json" "$OUT/candidate.json" > "$OUT/wrong-oracle.log" 2>&1; then
  echo 'corrupted discriminant type oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'structural enum discriminant type differs from independent rustc' "$OUT/wrong-oracle.log"
lake env lean tests/compiler_queries/DiscriminantType.lean
