#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
mkdir -p "$ROOT/scratch"
OUT="$(mktemp -d "$ROOT/scratch/foundation-startup-check.XXXXXX")"
# These are fresh source/compiler comparisons, not committed query catalogs.
printf 'fn main() {}\n' > "$OUT/main.rs"
bash tools/export-mir.sh --output "$OUT/foundation.json" --foundation --root main -- "$OUT/main.rs" --crate-name foundation_startup
bash tools/export-mir.sh --output "$OUT/schema12.json" --root main -- "$OUT/main.rs" --crate-name foundation_startup
python3 - "$OUT/no-core.rs" <<'PY_SOURCE'
from pathlib import Path
import sys
source=Path('exporter/fixtures/fail_closed/no_core.rs').read_text()
Path(sys.argv[1]).write_text(source.replace('#![no_core]', '#![no_core]\n#![no_main]'))
PY_SOURCE
bash tools/export-mir.sh --output "$OUT/no-core.json" --foundation --root identity -- "$OUT/no-core.rs" --crate-name startup_no_core
bash tools/export-mir.sh --output "$OUT/no-core-schema12.json" --root identity -- "$OUT/no-core.rs" --crate-name startup_no_core
python3 - "$OUT" <<'PY'
import json,pathlib,sys
out=pathlib.Path(sys.argv[1]); doc=json.loads((out/'schema12.json').read_text())
startup=doc['compiler_runtime_queries']['startup']; assert not startup['no_core']
entry=startup['core_escape_default']; identity=doc['definitions'][entry['definition']]
no_core=json.loads((out/'no-core-schema12.json').read_text())['compiler_runtime_queries']['startup']
assert no_core == {'no_core': True}
(out/'reference.json').write_text(json.dumps({'crate_index':identity['crate'],'index':identity['index'],'mir_available':entry['mir_available'],'no_core_comparison':no_core['no_core']}))
print('fresh startup outputs:',out)
PY
export ELAN_HOME="${ELAN_HOME:-$ROOT/.elan}"
flock /tmp/lean-miri-lake-build.lock "$ELAN_HOME/bin/lake" build Miri.Frontend.FoundationStartup
"$ELAN_HOME/bin/lake" env lean --run tests/foundation/FoundationStartup.lean "$OUT/foundation.json" "$OUT/reference.json" "$OUT/no-core.json"
