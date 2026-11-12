#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
"$RUSTC" -vV | rg -q "^commit-hash: $PIN$"
OUT="${FNDEF_MATERIAL_OUT:-$ROOT/scratch/fndef-material}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-fndef.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
"$RUSTC" --edition=2024 -Copt-level=0 tools/fndef-material-oracle.rs -o "$TEMP_DIR/oracle"
"$TEMP_DIR/oracle" --sysroot "$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}" \
  tests/repro/compiler-queries/fndef-identities.rs --crate-type=lib --crate-name=fndef_identities > "$OUT/oracle.json"
bash tools/export-mir.sh --output "$OUT/input.json" --root root -- \
  tests/repro/compiler-queries/fndef-identities.rs --crate-type=lib --crate-name=fndef_identities
flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.GenericInstantiation
lake env lean --run tests/compiler_queries/FnDefMaterial.lean
lake env lean --run tools/CompareFnDefMaterial.lean "$OUT/input.json" "$OUT/oracle.json"
python3 - "$OUT" <<'PY'
import json
import pathlib
import sys
out = pathlib.Path(sys.argv[1])
rows = json.loads((out / 'oracle.json').read_text())
rows[0]['expected']['definition']['index'] = 4294967295
(out / 'wrong-definition.json').write_text(json.dumps(rows))
PY
if lake env lean --run tools/CompareFnDefMaterial.lean "$OUT/input.json" "$OUT/wrong-definition.json" > "$OUT/wrong-definition.log" 2>&1; then
  printf 'mutated physical FnDef oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'generic type constructor absent from material and lazy arena' "$OUT/wrong-definition.log"
printf 'FnDef wrong-physical-definition oracle rejected as expected\n'
