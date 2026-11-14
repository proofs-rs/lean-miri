#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export CARGO_HOME="${CARGO_HOME:-$ROOT/.cargo}"
PIN=8144389c895da997dbdecaa635e41d6a50be6ffd
RUSTC="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/bin/rustc"
OUT="${VTABLE_SOURCE_SEGMENTS_OUT:-$ROOT/scratch/vtable-source-segments}"
mkdir -p "$OUT"
"$RUSTC" -vV | rg "^commit-hash: $PIN$" > /dev/null
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-${PIN:0:12}/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
TEMP_DIR="$(mktemp -d /tmp/lean-miri-vtable-segments.XXXXXXXX)"
trap 'rm -rf -- "$TEMP_DIR"' EXIT
"$RUSTC" --edition=2024 tools/vtable-source-segments-oracle.rs -o "$TEMP_DIR/oracle"
if [[ "${VTABLE_SOURCE_SEGMENTS_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.WorldVTableSegments Miri.Input.Decoder
fi
for MODE in false true; do
  SOURCE_FLAGS=()
  if [[ "$MODE" == true ]]; then SOURCE_FLAGS=(-Zno-trait-vptr); fi
  bash tools/export-mir.sh --output "$OUT/source-$MODE.json" --root vtable_root -- \
    tests/repro/compiler-queries/vtable-source-segments.rs --crate-type=lib \
    --crate-name=vtable_source_segments "${SOURCE_FLAGS[@]}"
  python3 - "$TEMP_DIR/oracle" "$OUT" "$MODE" <<'PY'
import json, pathlib, subprocess, sys
oracle, out, mode = sys.argv[1], pathlib.Path(sys.argv[2]), sys.argv[3]
source = json.loads((out / f'source-{mode}.json').read_text())
with (out / f'oracle-{mode}.json').open('w') as stdout, (out / f'oracle-{mode}.log').open('w') as stderr:
    subprocess.run([oracle, *source['invocation']['rustc_args']], stdout=stdout,
                   stderr=stderr, check=True, timeout=90)
PY
  lake env lean --run tests/compiler_queries/VTableSourceSegments.lean \
    "$OUT/source-$MODE.json" "$OUT/oracle-$MODE.json" "$MODE"
done
lake env lean --run tests/compiler_queries/VTableSourceSegments.lean \
  "$OUT/source-true.json" "$OUT/oracle-false.json" true > "$OUT/wrong-policy.log" 2>&1 && {
    printf 'vtable policy mismatch unexpectedly passed\n' >&2
    exit 1
  }
rg -q 'source World vtable segments differ from pinned compiler' "$OUT/wrong-policy.log"
printf 'vtable source policy mismatch rejection PASS\n'
