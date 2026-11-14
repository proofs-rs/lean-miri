#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export PATH="$(dirname "$RUSTC"):$PATH"
export LD_LIBRARY_PATH="$(dirname "$(dirname "$RUSTC")")/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${FUNCTION_POINTER_TYPE_HASH_OUT:-$(mktemp -d /tmp/lean-miri-function-pointer-hash.XXXXXXXX)}"
mkdir -p "$OUT"
cd "$ROOT"
if [[ -n "${FUNCTION_POINTER_TYPE_HASH_EXPORTER:-}" ]]; then
  "$FUNCTION_POINTER_TYPE_HASH_EXPORTER" --output "$OUT/source.json" --root fn_pointer_hashes -- \
    tests/compiler_queries/type-hash-function-pointer.rs --crate-name fnptr_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
else
  bash tools/export-mir.sh --output "$OUT/source.json" --root fn_pointer_hashes -- \
    tests/compiler_queries/type-hash-function-pointer.rs --crate-name fnptr_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
fi
"$RUSTC" --edition 2024 tools/function-pointer-type-hash-oracle.rs -o "$OUT/oracle"
"$RUSTC" --edition 2024 tools/open-region-type-hash-oracle.rs -o "$OUT/open-oracle"
python3 - "$OUT" <<'PY'
import json, pathlib, subprocess, sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as stdout:
    subprocess.run([str(out/'oracle'),*source['invocation']['rustc_args']],stdout=stdout,check=True,timeout=90)
with (out/'open-oracle.json').open('w') as stdout:
    subprocess.run([str(out/'open-oracle'),*source['invocation']['rustc_args']],stdout=stdout,check=True,timeout=90)
open_wrong=json.loads((out/'open-oracle.json').read_text()); open_wrong[0]['hash']=str(int(open_wrong[0]['hash'])+1)
(out/'open-wrong.json').write_text(json.dumps(open_wrong))
wrong=json.loads((out/'oracle.json').read_text()); wrong[0]['hash']=str(int(wrong[0]['hash'])+1)
(out/'wrong.json').write_text(json.dumps(wrong))
PY
if [[ "${FUNCTION_POINTER_TYPE_HASH_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.GenericInstantiationWorld Miri.Input.FunctionPointerStableHash Miri.Input.WorldTypeHash
fi
lake env lean --run tests/compiler_queries/FunctionPointerTypeHash.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/FunctionPointerTypeHash.lean "$OUT/source.json" "$OUT/wrong.json" >"$OUT/wrong.log" 2>&1; then
  echo 'incorrect function-pointer type hash oracle was accepted' >&2
  exit 1
fi
rg -q 'raw FnPtr/HRTB hash differs' "$OUT/wrong.log"
echo "PASS mutated function-pointer hash oracle rejected; evidence=$OUT"

lake env lean --run tests/compiler_queries/OpenRegionTypeHash.lean "$OUT/source.json" "$OUT/open-oracle.json"
lake env lean --run tests/compiler_queries/OpenRegionHashScope.lean
if lake env lean --run tests/compiler_queries/OpenRegionTypeHash.lean "$OUT/source.json" "$OUT/open-wrong.json" >"$OUT/open-wrong.log" 2>&1; then
  echo 'incorrect open-region type hash oracle was accepted' >&2
  exit 1
fi
rg -q 'open material raw hash differs' "$OUT/open-wrong.log"
echo "PASS mutated open-region hash oracle rejected; evidence=$OUT"
