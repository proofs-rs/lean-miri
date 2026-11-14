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
OUT="${PATTERN_TYPE_HASH_OUT:-$(mktemp -d /tmp/lean-miri-pattern-hash.XXXXXXXX)}"
mkdir -p "$OUT"
cd "$ROOT"
if [[ -n "${PATTERN_TYPE_HASH_EXPORTER:-}" ]]; then
  "$PATTERN_TYPE_HASH_EXPORTER" --output "$OUT/source.json" --root pattern_layouts -- \
    tests/compiler_queries/type-hash-pattern.rs --crate-name pattern_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
else
  bash tools/export-mir.sh --output "$OUT/source.json" --root pattern_layouts -- \
    tests/compiler_queries/type-hash-pattern.rs --crate-name pattern_hash_probe --crate-type lib --edition 2024 -Zmir-opt-level=0
fi
"$RUSTC" --edition 2024 tools/pattern-type-hash-oracle.rs -o "$OUT/oracle"
python3 - "$OUT" <<'PYCODE'
import json, pathlib, subprocess, sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'source.json').read_text())
patterns=[node for node in source['types'] if node['shape']['kind']=='pattern_type']
assert len(patterns)==7, 'fresh Pattern source domain incomplete'
assert all(node['compiler_facts'].get('type_id_hash') is None for node in patterns), 'covered Pattern retained eager TypeId hash'
with (out/'oracle.json').open('w') as stdout:
    subprocess.run([str(out/'oracle'),*source['invocation']['rustc_args']],stdout=stdout,check=True,timeout=90)
wrong=json.loads((out/'oracle.json').read_text()); wrong[0]['hash']=str(int(wrong[0]['hash'])+1)
(out/'wrong.json').write_text(json.dumps(wrong))
PYCODE
if [[ "${PATTERN_TYPE_HASH_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.GenericInstantiationWorld Miri.Input.WorldTypeHash
fi
lake env lean --run tests/compiler_queries/PatternTypeHash.lean "$OUT/source.json" "$OUT/oracle.json"
lake env lean --run tests/compiler_queries/PatternTypeHashMalformed.lean
if lake env lean --run tests/compiler_queries/PatternTypeHash.lean "$OUT/source.json" "$OUT/wrong.json" >"$OUT/wrong.log" 2>&1; then
  echo 'incorrect Pattern type hash oracle was accepted' >&2
  exit 1
fi
rg -q 'Pattern raw material hash differs' "$OUT/wrong.log"
echo "PASS mutated Pattern hash oracle rejected; evidence=$OUT"
