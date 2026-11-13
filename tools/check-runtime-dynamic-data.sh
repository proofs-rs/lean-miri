#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${RUNTIME_DYNAMIC_DATA_OUT:-$ROOT/scratch/runtime-dynamic-data}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d /tmp/lean-miri-dynamic-data.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/runtime-dynamic-data-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${RUNTIME_DYNAMIC_DATA_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.CompilerVTableLeaves Miri.Input.Decoder
fi
for CONTROL in const generic; do
  if "$RUSTC" --edition=2024 --crate-type=lib --emit=metadata "tests/repro/compiler-queries/runtime-dynamic-$CONTROL-negative.rs" -o "$TEMP_DIR/$CONTROL.rmeta" > "$OUT/$CONTROL-negative.log" 2>&1; then
    printf 'invalid dynamic source unexpectedly typechecked\n'
    exit 1
  fi
  if [[ "$CONTROL" == const ]]; then
    rg -q 'E0038' "$OUT/$CONTROL-negative.log"
  else
    rg -q 'E0277' "$OUT/$CONTROL-negative.log"
  fi
done
for MODE in plain kcfi plain-no-vptr kcfi-no-vptr; do
  FLAGS=()
  if [[ "$MODE" == *no-vptr ]]; then FLAGS+=(-Zno-trait-vptr); fi
  if [[ "$MODE" == kcfi* ]]; then
    # Query-only comparison against prebuilt unsanitized core, not linked guest ABI.
    FLAGS+=(-Zsanitizer=kcfi -Clto -Cpanic=abort -Cunsafe-allow-abi-mismatch=sanitizer)
  fi
  bash tools/export-mir.sh --output "$OUT/$MODE-source.json" --root dynamic_root -- tests/repro/compiler-queries/runtime-dynamic-data.rs --edition=2024 --crate-type=lib --crate-name=runtime_dynamic_data "${FLAGS[@]}"
  python3 - "$TEMP_DIR/oracle" "$OUT" "$MODE" <<'PY'
import json,pathlib,subprocess,sys
oracle,out,mode=sys.argv[1],pathlib.Path(sys.argv[2]),sys.argv[3]
source=json.loads((out/f'{mode}-source.json').read_text())
with (out/f'{mode}-oracle.json').open('w') as stdout,(out/f'{mode}-oracle.log').open('w') as stderr:
    subprocess.run([oracle,*source['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=90)
changed=json.loads((out/f'{mode}-oracle.json').read_text())
row=next(row for row in changed['queries'] if row['name']=='query_projection')
projection=next(child for child in row['dynamic']['children'] if child.get('kind')=='binder' and child['value'].get('tag')=='projection')
term=projection['value']['children'][-1]
assert term=={'kind':'atom','sort':'type','tag':'uint','payload':'u8'}
term['payload']='u16'
(out/f'{mode}-wrong-oracle.json').write_text(json.dumps(changed))
PY
  lake env lean --run tests/compiler_queries/RuntimeDynamicData.lean "$OUT/$MODE-source.json" "$OUT/$MODE-oracle.json"
  if lake env lean --run tests/compiler_queries/RuntimeDynamicData.lean "$OUT/$MODE-source.json" "$OUT/$MODE-wrong-oracle.json" > "$OUT/$MODE-wrong-oracle.log" 2>&1; then
    printf 'mutated dynamic source oracle unexpectedly passed\n'
    exit 1
  fi
  rg -q 'typed Dynamic oracle differs from raw source declaration' "$OUT/$MODE-wrong-oracle.log"
done
printf 'runtime typed Dynamic callbacks and suffix guards PASS\n'
