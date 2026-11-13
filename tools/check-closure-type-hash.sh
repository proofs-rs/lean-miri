#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export PATH="$(dirname "$RUSTC"):$PATH"
export LD_LIBRARY_PATH="$(dirname "$(dirname "$RUSTC")")/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${CLOSURE_TYPE_HASH_OUT:-$(mktemp -d /tmp/lean-miri-closure-hash.XXXXXXXX)}"
mkdir -p "$OUT"
if [[ -n "${CLOSURE_TYPE_HASH_EXPORTER:-}" ]]; then
  "$CLOSURE_TYPE_HASH_EXPORTER" --output "$OUT/source.json" --root closure_hashes -- \
    tests/compiler_queries/type-hash-closure.rs --crate-name closure_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
else
  bash tools/export-mir.sh --output "$OUT/source.json" --root closure_hashes -- \
    tests/compiler_queries/type-hash-closure.rs --crate-name closure_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
fi
"$RUSTC" --edition 2024 tools/closure-type-hash-oracle.rs -o "$OUT/oracle"
python3 - "$OUT" <<'PYCODE'
import json,pathlib,subprocess,sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'source.json').read_text())
closures=[node for node in source['types'] if node['shape']['kind']=='closure']
assert len(closures)==8, 'fresh closure source domain incomplete'
assert all(node['compiler_facts'].get('type_id_hash') is None for node in closures), 'covered Closure retained eager TypeId hash'
with (out/'oracle.json').open('w') as stdout:
    subprocess.run([str(out/'oracle'),*source['invocation']['rustc_args']],stdout=stdout,check=True,timeout=90)
wrong=json.loads((out/'oracle.json').read_text()); wrong[0]['hash']=str(int(wrong[0]['hash'])+1)
(out/'wrong.json').write_text(json.dumps(wrong))
PYCODE
if [[ "${CLOSURE_TYPE_HASH_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.WorldTypeHash Miri.Input.TypeArenaPredicateWorld
fi
lake env lean --run tests/compiler_queries/ClosureTypeHash.lean "$OUT/source.json" "$OUT/oracle.json"
lake env lean --run tests/compiler_queries/TypeArenaPredicates.lean
if lake env lean --run tests/compiler_queries/ClosureTypeHash.lean "$OUT/source.json" "$OUT/wrong.json" > "$OUT/wrong.log" 2>&1; then
  echo 'incorrect Closure type hash oracle accepted' >&2
  exit 1
fi
rg -q 'raw Closure hash differs' "$OUT/wrong.log"
echo "PASS mutated Closure hash oracle rejected; evidence=$OUT"
