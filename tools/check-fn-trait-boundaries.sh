#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
OUT="${FN_TRAIT_BOUNDARIES_OUT:-$ROOT/scratch/fn-trait-boundaries}"
mkdir -p "$OUT"
EXPORT_COMMAND=(bash tools/export-mir.sh)
if [[ -n "${MIRI_SEALED_EXPORTER:-}${MIRI_SEALED_EXPORTER_MANIFEST:-}" ]]; then EXPORT_COMMAND=(bash tools/run-sealed-exporter.sh); fi
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
TEMP_DIR="$(mktemp -d "${TMPDIR:-/tmp}/lean-miri-fn-boundaries.XXXXXXXX")"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/fn-trait-async-closure-oracle.rs -o "$TEMP_DIR/async-oracle"
"$RUSTC" --edition=2024 tools/fn-trait-nested-pointer-oracle.rs -o "$TEMP_DIR/nested-oracle"
if [[ "${FN_TRAIT_BOUNDARIES_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.SourceFnTraits Miri.Input.AliasRuntime Miri.Input.Decoder
fi
"${EXPORT_COMMAND[@]}" --output "$OUT/async-source.json" --root async_root -- tests/repro/compiler-queries/fn-trait-async-closure-boundary.rs --edition=2024 --crate-type=lib --crate-name=async_closure_boundary
"${EXPORT_COMMAND[@]}" --output "$OUT/nested-source.json" --root nested_root -- tests/repro/compiler-queries/fn-trait-nested-pointer-boundary.rs --edition=2024 --crate-type=lib --crate-name=nested_fn_pointer
python3 - "$TEMP_DIR" "$OUT" <<'PY'
import json,pathlib,subprocess,sys
binary,out=map(pathlib.Path,sys.argv[1:])
for mode in ['nested','async']:
    source=json.loads((out/f'{mode}-source.json').read_text())
    with (out/f'{mode}-oracle.json').open('w') as f:subprocess.run([str(binary/f'{mode}-oracle'),*source['invocation']['rustc_args']],stdout=f,check=True)
PY
lake env lean --run tests/compiler_queries/FnTraitBoundaries.lean "$OUT/nested-source.json" "$OUT/nested-oracle.json" "$OUT/async-source.json" "$OUT/async-oracle.json"
printf 'ground Fn candidate type/header boundaries PASS\n'
