#!/usr/bin/env bash
# Compare source ValTrees with actual rustc Const::eval answers from the same fixture.
# The oracle exporter must differ only by disabling raw_type_constant_eligible.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${RAW_AGGREGATE_OUT:?set RAW_AGGREGATE_OUT to a private output directory}"
CANDIDATE="${RAW_AGGREGATE_CANDIDATE_TARGET:?set immutable candidate target}"
ORACLE="${RAW_AGGREGATE_ORACLE_TARGET:?set immutable admission-disabled oracle target}"
mkdir -p "$OUT"
for version in candidate oracle; do
  target="$CANDIDATE"
  if [[ "$version" == oracle ]]; then target="$ORACLE"; fi
  LEAN_MIRI_TRACE_CONST_EVAL=1 CARGO_TARGET_DIR="$target" bash tools/export-mir.sh \
    --output "$OUT/$version.json" --root miri_start -- \
    tests/repro/compiler-queries/raw-aggregate-type-constants.rs \
    --crate-name=raw_aggregate_type_constants --edition=2024 -Cpanic=abort -Zmir-opt-level=0 \
    > "$OUT/$version.stdout" 2> "$OUT/$version.trace"
done
python3 - "$OUT" <<'PY'
from collections import Counter
from pathlib import Path
import re,sys
out=Path(sys.argv[1]); pattern=re.compile(r'^lean_miri_const_call route=(\S+) queried=(true|false) category=(\S+) value=(.*)$')
def rows(name):
    return [m.groups() for line in (out/(name+'.trace')).read_text().splitlines() if (m:=pattern.match(line))]
before,after=rows('oracle'),rows('candidate')
old=Counter(v for r,q,c,v in before if r=='mir_eval' and q=='true' and c=='ty')
raw=Counter(v for r,q,c,v in after if r=='raw_type' and q=='false' and c=='ty')
remaining=Counter(v for r,q,c,v in after if q=='true' and c=='ty')
assert len(raw)==10, f'expected ten actual source ValTrees, got {len(raw)}'
for value,count in raw.items():
    assert count==2 and old[value]==count and not remaining[value], (value,count,old[value],remaining[value])
    print(f'PASS {value}: explicit Const::eval calls {count}->0')
assert len(remaining)==2 and all(count==2 for count in remaining.values()), remaining
print('PASS pair/repr(C) allocation residuals retain explicit evaluation')
PY
lake env lean --run tests/compiler_queries/AggregateTypeConstants.lean \
  "$OUT/candidate.json" "$OUT/oracle.json"
