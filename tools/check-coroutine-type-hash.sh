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
OUT="${COROUTINE_TYPE_HASH_OUT:-$(mktemp -d /tmp/lean-miri-coroutine-hash.XXXXXXXX)}"
mkdir -p "$OUT"
if [[ -n "${COROUTINE_TYPE_HASH_EXPORTER:-}" ]]; then
  "$COROUTINE_TYPE_HASH_EXPORTER" --output "$OUT/source.json" --root coroutine_hashes -- \
    tests/compiler_queries/type-hash-coroutine.rs --crate-name coroutine_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0 -Cpanic=abort
else
  bash tools/export-mir.sh --output "$OUT/source.json" --root coroutine_hashes -- \
    tests/compiler_queries/type-hash-coroutine.rs --crate-name coroutine_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0 -Cpanic=abort
fi
if [[ -n "${COROUTINE_TYPE_HASH_ORACLE:-}" ]]; then
  # The caller supplies an oracle built against the same compiler/metadata as
  # COROUTINE_TYPE_HASH_EXPORTER; the input flags come from its fresh document.
  cp -- "$COROUTINE_TYPE_HASH_ORACLE" "$OUT/oracle"
else
  "$RUSTC" --edition 2024 tools/coroutine-type-hash-oracle.rs -o "$OUT/oracle"
fi
python3 - "$OUT" <<'PYCODE'
import json,pathlib,subprocess,sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'source.json').read_text())
coroutines=[node for node in source['types'] if node['shape']['kind']=='coroutine']
assert len(coroutines)==4, 'fresh coroutine source domain incomplete'
assert all(node['compiler_facts'].get('type_id_hash') is None for node in coroutines), 'covered Coroutine retained eager TypeId hash'
with (out/'oracle.json').open('w') as stdout:
    subprocess.run([str(out/'oracle'),*source['producer']['input_settings']['rustc_args']],stdout=stdout,check=True,timeout=90)
wrong=json.loads((out/'oracle.json').read_text()); wrong[0]['hash']=str(int(wrong[0]['hash'])+1)
(out/'wrong.json').write_text(json.dumps(wrong))
PYCODE
if [[ "${COROUTINE_TYPE_HASH_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.WorldTypeHash
fi
lake env lean --run tests/compiler_queries/CoroutineTypeHash.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/CoroutineTypeHash.lean "$OUT/source.json" "$OUT/wrong.json" > "$OUT/wrong.log" 2>&1; then
  echo 'incorrect Coroutine type hash oracle accepted' >&2
  exit 1
fi
rg -q 'raw Coroutine hash differs' "$OUT/wrong.log"
echo "PASS mutated Coroutine hash oracle rejected; evidence=$OUT"
