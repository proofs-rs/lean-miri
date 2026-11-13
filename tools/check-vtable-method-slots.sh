#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${VTABLE_METHOD_SLOTS_OUT:-$ROOT/scratch/vtable-method-slots}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
bash tools/export-mir.sh --output "$OUT/source.json" --root slots_root -- tests/repro/compiler-queries/vtable-method-slots.rs --crate-type=lib --crate-name=vtable_method_slots
TEMP_DIR="$(mktemp -d /tmp/lean-miri-vtable-slots.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/vtable-method-slots-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
oracle,out=sys.argv[1],pathlib.Path(sys.argv[2])
source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as stdout, (out/'oracle.log').open('w') as stderr:
    subprocess.run([oracle,*source['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=90)
changed=json.loads((out/'oracle.json').read_text())
changed['queries'][-1]['entries'][-1]={'kind':'by_value_shim','definition':{'crate':0,'index':0},'arguments':[]}
(out/'wrong-oracle.json').write_text(json.dumps(changed))
PY
if [[ "${VTABLE_METHOD_SLOTS_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.WorldVTableMethods Miri.Input.Decoder
fi
lake env lean --run tests/compiler_queries/VTableMethodSlots.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/VTableMethodSlots.lean "$OUT/source.json" "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  printf 'mutated vtable slot oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'raw slots differ from pinned rustc' "$OUT/wrong-oracle.log"
printf 'vtable method slot mutated oracle rejection PASS\n'
