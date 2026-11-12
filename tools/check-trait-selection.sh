#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
"$RUSTC" -vV | rg -q "^commit-hash: $PIN$"
OUT="${TRAIT_SELECTION_OUT:-$ROOT/scratch/trait-selection}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-trait-selection.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
bash tools/export-mir.sh --output "$OUT/candidate.json" --root trait_program_root -- \
  tests/repro/compiler-queries/trait-program.rs --crate-type=lib --crate-name=trait_program -Zmir-opt-level=0
"$RUSTC" --edition=2024 tools/trait-selection-oracle.rs -o "$TEMP_DIR/oracle"
# Execute the independent query oracle with the exact effective compiler args
# recorded by this fresh producer, including sysroot/cfg/encoding settings.
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'candidate.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout, stderr=stderr, check=True, timeout=90)
rows = json.loads((out / 'oracle.json').read_text())
wrong = json.loads(json.dumps(rows))
next(r for r in wrong if not r['outside_scope'] and r['expected']['kind'] == 'implementation')['expected']['definition']['index'] += 1
(out / 'wrong-selected-impl.json').write_text(json.dumps(wrong))
PY
if [[ "${TRAIT_SELECTION_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.AliasRuntime
fi
lake env lean --run tools/CompareTraitSelection.lean "$OUT/candidate.json" "$OUT/oracle.json"
if lake env lean --run tools/CompareTraitSelection.lean "$OUT/candidate.json" "$OUT/wrong-selected-impl.json" > "$OUT/wrong-selected-impl.log" 2>&1; then
  printf 'corrupted selected-impl oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'selected source impl/substitution differs from rustc' "$OUT/wrong-selected-impl.log"
printf 'trait selection wrong-impl negative control PASS\n'
