#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 CARGO_INCREMENTAL=0 CARGO_BUILD_JOBS=1
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
: "${MIRI_SEALED_EXPORTER:?set immutable exporter binary}"
: "${MIRI_SEALED_EXPORTER_MANIFEST:?set immutable exporter manifest}"
OUT="${ORDINARY_TRAIT_DEFAULT_OUT:-$ROOT/scratch/ordinary-trait-default}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-ordinary-default.XXXXXXXX")"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 -C debuginfo=0 -C strip=debuginfo tools/ordinary-trait-default-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${ORDINARY_TRAIT_DEFAULT_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.SourceMirCall Miri.Input.WorldDeducedAbi Miri.Input.Decoder
fi
bash tools/run-sealed-exporter.sh --output "$OUT/source.json" -- tests/repro/compiler-queries/ordinary-trait-default.rs --edition=2024 --crate-type=lib --crate-name=ordinary_trait_default
python3 - "$TEMP_DIR/oracle" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
binary,out=map(pathlib.Path,sys.argv[1:]);source=json.loads((out/'source.json').read_text())
with (out/'oracle.json').open('w') as f:subprocess.run([str(binary),*source['invocation']['rustc_args']],stdout=f,check=True)
wrong=json.loads((out/'oracle.json').read_text());assert len(wrong['queries'])==2
wrong['queries'][0]['selected']=wrong['queries'][1]['selected']
(out/'wrong-oracle.json').write_text(json.dumps(wrong))
PY
lake env lean --run tests/compiler_queries/OrdinaryTraitDefault.lean "$OUT/source.json" "$OUT/oracle.json"
if lake env lean --run tests/compiler_queries/OrdinaryTraitDefault.lean "$OUT/source.json" "$OUT/wrong-oracle.json" > "$OUT/wrong-oracle.log" 2>&1; then
  echo 'wrong default trait physical leaf oracle unexpectedly accepted' >&2; exit 1
fi
rg -F 'ordinary source impl Item/rebased args differ from rustc try_resolve' "$OUT/wrong-oracle.log" > /dev/null
printf 'ordinary trait defaults preserve trait arguments and raw body identity PASS\n'
