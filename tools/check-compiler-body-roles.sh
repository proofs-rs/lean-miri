#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
OUT="${COMPILER_BODY_ROLE_OUT:?set private output directory}"
mkdir -p "$OUT"
bash tools/export-mir.sh --output "$OUT/source.json" --root miri_start -- \
  tests/repro/compiler-queries/generic-mir-call-start.rs --crate-name generic_mir_call_start \
  --edition=2021 -Zmir-opt-level=0 -Cpanic=abort > "$OUT/export.stdout" 2> "$OUT/export.stderr"
lake env lean --run tests/compiler_queries/CompilerBodyRoles.lean "$OUT/source.json"
lake env lean --run tests/compiler_queries/CompilerTypingEnv.lean
python3 - "$OUT" <<'PY'
from pathlib import Path
import copy,json,sys
out=Path(sys.argv[1]);source=json.loads((out/'source.json').read_text())
for domain in ['body','template']:
  for role in ['missing','unknown']:
    changed=copy.deepcopy(source)
    target=next(body for body in changed['bodies'] if 'source_role' in body) if domain=='body' else changed['mir_templates'][0]
    if role=='missing': del target['source_role']
    else: target['source_role']='unknown_future_role'
    (out/(domain+'-'+role+'.json')).write_text(json.dumps(changed))
PY
for role in body-missing body-unknown template-missing template-unknown; do
  lake env lean --run tests/compiler_queries/CompilerBodyRoleDecode.lean "$OUT/$role.json" role
done
