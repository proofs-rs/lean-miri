#!/usr/bin/env bash
# Independent pinned-rustc Sized/MetaSized goals, including novel ADT terms.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
cd "$ROOT"
OUT="${TERM_SIZED_OUT:-$ROOT/scratch/term-sized}"
mkdir -p "$OUT"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
"$RUSTC" -vV > "$OUT/rustc-version.txt"
rg -q "^commit-hash: $PIN$" "$OUT/rustc-version.txt"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-term-sized.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
bash tools/export-mir.sh --output "$OUT/candidate.json" --root term_sized_root -- \
  tests/repro/compiler-queries/term-sized.rs --crate-type=lib --crate-name=term_sized_probe
"$RUSTC" --edition=2024 tools/term-sized-oracle.rs -o "$TEMP_DIR/oracle"
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
oracle,out=sys.argv[1],pathlib.Path(sys.argv[2]);value=json.loads((out/'candidate.json').read_text())
with (out/'oracle.json').open('w') as stdout,(out/'oracle.log').open('w') as stderr:
    subprocess.run([oracle,*value['invocation']['rustc_args']],stdout=stdout,stderr=stderr,check=True,timeout=90)
rows=json.loads((out/'oracle.json').read_text());assert len(rows)==9
wrong=json.loads(json.dumps(rows));wrong[-1]['is_sized']=not wrong[-1]['is_sized'];(out/'wrong-oracle.json').write_text(json.dumps(wrong))
PY
if [[ "${TERM_SIZED_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.AliasRuntime Miri.Input.TermSized
fi
lake env lean --run tools/CompareTermSized.lean "$OUT/candidate.json" "$OUT/oracle.json"
if lake env lean --run tools/CompareTermSized.lean "$OUT/candidate.json" "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  echo 'corrupted term Sized oracle unexpectedly passed' >&2
  exit 1
fi
rg -q 'term is_sized differs from independent pinned rustc' "$OUT/wrong-oracle.log"
