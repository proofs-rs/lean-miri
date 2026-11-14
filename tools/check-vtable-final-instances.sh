#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${VTABLE_FINAL_INSTANCES_OUT:-$ROOT/scratch/vtable-final-instances}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-vtable-instances.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/vtable-final-instance-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${VTABLE_FINAL_INSTANCES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.CompilerVirtualLeaves Miri.Input.CompilerInstanceAbi Miri.Input.Decoder
fi
for MODE in plain kcfi; do
  FLAGS=()
  if [[ "$MODE" == kcfi ]]; then
    # Analysis/query-only comparison against the prebuilt unsanitized core.
    # No generated guest, linked executable or sanitizer ABI is tested here.
    FLAGS=(-Zsanitizer=kcfi -Clto -Cpanic=abort -Cunsafe-allow-abi-mismatch=sanitizer)
  fi
  bash tools/export-mir.sh --output "$OUT/$MODE-source.json" --root instance_root -- tests/repro/compiler-queries/vtable-final-instance.rs --crate-type=lib --crate-name=vtable_final_instance "${FLAGS[@]}"
  python3 - "$TEMP_DIR/oracle" "$OUT" "$MODE" <<'PY'
import json,pathlib,subprocess,sys
oracle,out,mode=sys.argv[1],pathlib.Path(sys.argv[2]),sys.argv[3]
source=json.loads((out/f'{mode}-source.json').read_text())
with (out/f'{mode}-oracle.json').open('w') as stdout, (out/f'{mode}-oracle.log').open('w') as stderr:
    subprocess.run([oracle,*source['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=90)
changed=json.loads((out/f'{mode}-oracle.json').read_text())
changed['queries'][0]['entries'][1]['kind']='selected'
(out/f'{mode}-wrong-oracle.json').write_text(json.dumps(changed))
raw_changed=json.loads((out/f'{mode}-oracle.json').read_text())
raw=next(entry for row in raw_changed['queries'] for entry in row['raw_static'] if entry['result']['kind']=='by_value_shim')
assert raw['result']['arguments'][-1]['tag']=='static'
raw['result']['arguments'][-1]['tag']='erased'
(out/f'{mode}-wrong-raw-oracle.json').write_text(json.dumps(raw_changed))
PY
  lake env lean --run tests/compiler_queries/VTableInstances.lean "$OUT/$MODE-source.json" "$OUT/$MODE-oracle.json"
  if lake env lean --run tests/compiler_queries/VTableInstances.lean "$OUT/$MODE-source.json" "$OUT/$MODE-wrong-oracle.json" > "$OUT/$MODE-wrong-oracle.log" 2>&1; then
    printf 'mutated final-instance oracle unexpectedly passed\n' >&2
    exit 1
  fi
  rg -q 'final declarations differ from rustc' "$OUT/$MODE-wrong-oracle.log"
  if lake env lean --run tests/compiler_queries/VTableInstances.lean "$OUT/$MODE-source.json" "$OUT/$MODE-wrong-raw-oracle.json" > "$OUT/$MODE-wrong-raw-oracle.log" 2>&1; then
    printf 'mutated raw Static method oracle unexpectedly passed\n' >&2
    exit 1
  fi
  rg -q 'raw static method result differs from rustc' "$OUT/$MODE-wrong-raw-oracle.log"
done
printf 'final vtable instance policy and mutated-oracle comparisons PASS\n'
