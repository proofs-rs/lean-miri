#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
compiler_version_info="$("$RUSTC" -vV)"
rg -q "^commit-hash: $PIN$" <<< "$compiler_version_info"
OUT="${ENVIRONMENT_BOUNDS_OUT:-$ROOT/scratch/environment-bounds}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-environment-bounds.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
timeout 90 bash tools/export-mir.sh --output "$OUT/candidate.json" --root environment_bounds_root -- \
  tests/repro/compiler-queries/environment-bounds.rs --crate-type=lib --crate-name=environment_bounds -Zmir-opt-level=0
"$RUSTC" --edition=2024 tools/environment-bounds-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'candidate.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout, stderr=stderr, check=True, timeout=90)
PY
if [[ "${ENVIRONMENT_BOUNDS_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.TraitSelection.EnvironmentEntailment
fi
lake env lean tests/compiler_queries/EnvironmentEntailment.lean
lake env lean --run tools/CompareEnvironmentBounds.lean "$OUT/candidate.json" "$OUT/oracle.json"
