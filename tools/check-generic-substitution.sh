#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
if ! "$RUSTC" -vV | rg -q "^commit-hash: $PIN$"; then
  printf 'generic substitution oracle requires pinned rustc\n' >&2
  exit 1
fi
OUT="${GENERIC_SUBSTITUTION_OUT:-$ROOT/scratch/generic-substitution}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-substitution.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
"$RUSTC" --edition=2024 -C opt-level=0 tools/generic-substitution-oracle.rs -o "$TEMP_DIR/oracle"
"$TEMP_DIR/oracle" --sysroot "$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}" \
  tests/repro/compiler-queries/generic-substitution.rs --crate-type=lib \
  --crate-name=generic_substitution > "$OUT/oracle.json"
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.GenericMaterialCodec Miri.Input.GenericInstantiation
lake env lean --run tests/compiler_queries/GenericSubstitution.lean
lake env lean --run tests/compiler_queries/GenericInstantiation.lean
lake env lean --run tools/CompareGenericSubstitution.lean "$OUT/oracle.json"
python3 - "$OUT" <<'PY'
import copy
import json
import pathlib
import sys

out = pathlib.Path(sys.argv[1])
rows = json.loads((out / 'oracle.json').read_text())
def change_bound(value):
    if isinstance(value, dict):
        if value.get('kind') == 'bound' and isinstance(value.get('index'), int):
            value['index'] += 1
            return True
        return any(change_bound(child) for child in value.values())
    if isinstance(value, list):
        return any(change_bound(child) for child in value)
    return False
wrong_bound = copy.deepcopy(rows)
assert change_bound(wrong_bound[0]['expected'])
(out / 'wrong-bound.json').write_text(json.dumps(wrong_bound))
missing_argument = copy.deepcopy(rows)
missing_argument[0]['arguments'] = []
(out / 'missing-argument.json').write_text(json.dumps(missing_argument))
(out / 'nested.json').write_text(json.dumps({
    'templates': [rows[0]['source_material'], rows[1]['source_material']],
    'sentinel': 43,
}))
PY
lake env lean --run tests/compiler_queries/GenericMaterialStreaming.lean "$OUT/nested.json"
if lake env lean --run tools/CompareGenericSubstitution.lean "$OUT/wrong-bound.json" > "$OUT/wrong-bound.log" 2>&1; then
  printf 'mutated bound-variable oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'rustc generic substitution mismatch' "$OUT/wrong-bound.log"
if lake env lean --run tools/CompareGenericSubstitution.lean "$OUT/missing-argument.json" > "$OUT/missing-argument.log" 2>&1; then
  printf 'missing generic arguments unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'generic template argument count mismatch' "$OUT/missing-argument.log"
printf 'generic substitution negative controls rejected their expected mismatches\n'
