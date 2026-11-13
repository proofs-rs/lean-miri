#!/usr/bin/env bash
# Caller must complete the primary Lake build before running these readers.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
: "${MIRI_SEALED_EXPORTER:?select immutable current exporter}"
: "${MIRI_SEALED_EXPORTER_MANIFEST:?select matching source seal}"
: "${RUSTUP_HOME:?select pinned rustup home}"
TOOLCHAIN="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d"
export LD_LIBRARY_PATH="$TOOLCHAIN/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${OBJECT_MANUAL_IMPL_OUT:-$ROOT/scratch/object-candidate-manual-impl}"
mkdir -p "$OUT"
"$TOOLCHAIN/bin/rustc" --edition=2024 tools/object-manual-impl-oracle.rs -o "$OUT/oracle" > "$OUT/oracle-build.log" 2>&1
bash tools/run-sealed-exporter.sh --output "$OUT/source.json" --root miri_start -- tests/repro/compiler-queries/virtual-abi-runtime.rs --crate-type=bin --crate-name=virtual_abi_runtime --edition=2024 -Copt-level=0 -Cpanic=abort > "$OUT/export.log" 2>&1
python3 - "$OUT" <<'PY'
import json,pathlib,subprocess,sys
out=pathlib.Path(sys.argv[1]);source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as stdout,(out/'oracle.log').open('w') as stderr:
    subprocess.run([str(out/'oracle'),*source['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True)
changed=json.loads((out/'oracle.json').read_text())
method=changed['queries'][0]['methods'][0]
assert method['ordinary']['kind']=='virtual' and method['ordinary']['slot']==3
method['ordinary']['slot']=4
(out/'wrong-oracle.json').write_text(json.dumps(changed))
PY
lake env lean --run tests/compiler_queries/ObjectCandidateManualImpl.lean "$OUT/source.json" "$OUT/oracle.json" > "$OUT/positive.log" 2>&1
if lake env lean --run tests/compiler_queries/ObjectCandidateManualImpl.lean "$OUT/source.json" "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  echo 'corrupted ordinary Virtual slot unexpectedly accepted' >&2
  exit 1
fi
rg -q 'actual manual-catalog Virtual differs from rustc try_resolve' "$OUT/wrong-oracle.log"
cat "$OUT/positive.log"
