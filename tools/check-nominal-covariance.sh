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
OUT="${NOMINAL_COVARIANCE_OUT:-$(mktemp -d /tmp/lean-miri-nominal-covariance.XXXXXXXX)}"
mkdir -p "$OUT"
cd "$ROOT"
if [[ -n "${NOMINAL_COVARIANCE_EXPORTER:-}" ]]; then
  LEAN_MIRI_TRACE_COVARIANCE_CALLS=1 "$NOMINAL_COVARIANCE_EXPORTER" --output "$OUT/source.json" --root nominal_covariance_root -- \
    tests/repro/compiler-queries/nominal-covariance.rs --crate-name nominal_covariance --crate-type lib --edition 2024 -Zmir-opt-level=0 \
    >"$OUT/export.stdout" 2>"$OUT/export.trace"
else
  LEAN_MIRI_TRACE_COVARIANCE_CALLS=1 bash tools/export-mir.sh --output "$OUT/source.json" --root nominal_covariance_root -- \
    tests/repro/compiler-queries/nominal-covariance.rs --crate-name nominal_covariance --crate-type lib --edition 2024 -Zmir-opt-level=0 \
    >"$OUT/export.stdout" 2>"$OUT/export.trace"
fi
"$RUSTC" --edition 2024 tools/nominal-covariance-oracle.rs -o "$OUT/oracle"
python3 - "$OUT" <<'PY'
import json,pathlib,subprocess,sys
out=pathlib.Path(sys.argv[1]);source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as output:
    subprocess.run([str(out/'oracle'),*source['invocation']['rustc_args']],stdout=output,check=True,timeout=90)
trace=(out/'export.trace').read_text().splitlines()
nominal=[line for line in trace if 'source=Co<u8> target=Co<u16>' in line]
assert len(nominal)==1 and 'queried=false' in nominal[0], 'nominal relation query was not omitted'
wrong=json.loads((out/'oracle.json').read_text());wrong['relations'][1]['value']=not wrong['relations'][1]['value']
(out/'wrong.json').write_text(json.dumps(wrong))
PY
if [[ "${NOMINAL_COVARIANCE_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.CompilerCovariance Miri.Input.TableTail
fi
lake env lean --run tests/compiler_queries/NominalCovariance.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/NominalCovariance.lean "$OUT/source.json" "$OUT/wrong.json" >"$OUT/wrong.log" 2>&1; then
  echo 'incorrect nominal covariance oracle accepted' >&2
  exit 1
fi
rg -q 'independent nominal covariance mismatch' "$OUT/wrong.log"
echo "PASS nominal covariance query omission and mutated oracle rejection; evidence=$OUT"
