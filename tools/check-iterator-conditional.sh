#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
SOURCE="${1:?pass the immutable exported std fixture containing FnDef type 1257}"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${ITERATOR_CONDITIONAL_OUT:-$ROOT/scratch/iterator-conditional}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-iterator.XXXXXXXX")"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/std-iterator-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${ITERATOR_CONDITIONAL_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.SourceBuiltinDispatch Miri.Input.AliasRuntime Miri.Input.Decoder
fi
python3 - "$TEMP_DIR/oracle" "$SOURCE" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
binary,source,out=map(pathlib.Path,sys.argv[1:])
document=json.loads(source.read_text())
with (out/'oracle.json').open('w') as f:
    subprocess.run([str(binary),*document['invocation']['rustc_args']],stdout=f,check=True)
wrong=json.loads((out/'oracle.json').read_text())
positive=[q for q in wrong['iterator_goals'] if q['result']['kind']=='implementation']
assert len(positive)==1
positive[0]['result']['definition']['index']+=1
(out/'wrong-impl-oracle.json').write_text(json.dumps(wrong))
PY
lake env lean --run tests/compiler_queries/IteratorConditional.lean "$SOURCE" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/IteratorConditional.lean "$SOURCE" "$OUT/wrong-impl-oracle.json" > "$OUT/wrong-impl.log" 2>&1; then
  echo 'wrong physical impl oracle unexpectedly accepted' >&2; exit 1
fi
rg -F 'actual Iterator selected a different physical impl' "$OUT/wrong-impl.log" > /dev/null
printf 'conditional Iterator compiler candidate absence and physical manual selection PASS\n'
