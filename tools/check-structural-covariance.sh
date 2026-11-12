#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${STRUCTURAL_COVARIANCE_OUT:-$ROOT/scratch/structural-covariance}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg -q "^commit-hash: $PIN$"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
bash tools/export-mir.sh --output "$OUT/candidate.json" --root covariance_root -- \
  tests/repro/compiler-queries/structural-covariance.rs --crate-type=lib --crate-name=structural_covariance
TEMP_DIR="$(mktemp -d /tmp/lean-miri-covariance.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/structural-covariance-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'candidate.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout,
                   stderr=stderr, check=True, timeout=90)
rows = json.loads((out / 'oracle.json').read_text())
rows[1]['value'] = not rows[1]['value']
(out / 'wrong-oracle.json').write_text(json.dumps(rows))
PY
if [[ "${STRUCTURAL_COVARIANCE_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.CompilerCovariance Miri.Input.Decoder
fi
lake env lean --run tests/compiler_queries/StructuralCovariance.lean "$OUT/candidate.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/StructuralCovariance.lean "$OUT/candidate.json" \
    "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  printf 'corrupted covariance oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'independent rustc structural covariance mismatch' "$OUT/wrong-oracle.log"
printf 'structural covariance mutated-oracle rejection PASS\n'
