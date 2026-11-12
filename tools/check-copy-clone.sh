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
OUT="${COPY_CLONE_OUT:-$ROOT/scratch/copy-clone}"
mkdir -p "$OUT"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-copy-clone.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
cd "$ROOT"
timeout 90 bash tools/export-mir.sh --output "$OUT/candidate.json" --root copy_clone_root -- \
  tests/repro/compiler-queries/copy-clone-program.rs --crate-type=lib --crate-name=copy_clone_program -Zmir-opt-level=0
"$RUSTC" --edition=2024 tools/copy-clone-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json, pathlib, subprocess, sys
oracle, out = sys.argv[1], pathlib.Path(sys.argv[2])
source = json.loads((out / 'candidate.json').read_text())
with (out / 'oracle.json').open('w') as stdout, (out / 'oracle.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout, stderr=stderr, check=True, timeout=90)
wrong = json.loads((out / 'oracle.json').read_text())
next(r for r in wrong if r['expected']['kind'] == 'implementation')['expected']['definition']['index'] += 1
(out / 'wrong-impl.json').write_text(json.dumps(wrong))
PY
if [[ "${COPY_CLONE_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.AliasRuntime
fi
lake env lean tests/compiler_queries/StructuralCopyClone.lean
lake env lean tests/compiler_queries/TraitSelectionMatch.lean
lake env lean tests/compiler_queries/TraitSelectionFulfill.lean
lake env lean --run tools/CompareCopyClone.lean "$OUT/candidate.json" "$OUT/oracle.json"
if lake env lean --run tools/CompareCopyClone.lean "$OUT/candidate.json" "$OUT/wrong-impl.json" > "$OUT/wrong-impl.log" 2>&1; then
  printf 'wrong Copy/Clone impl oracle unexpectedly passed\n' >&2
  exit 1
fi
rg -q 'Copy/Clone source impl/substitution mismatch' "$OUT/wrong-impl.log"
printf 'Copy/Clone wrong-impl negative control PASS\n'
