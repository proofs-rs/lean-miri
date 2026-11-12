#!/usr/bin/env bash
# Compare a frozen material-layout producer with the raw tagged/niche enum recipe producer.
# Both binaries must use the pinned rustc and the same source fixture. This
# runner does not rebuild or mutate either binary.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
if [[ $# != 2 ]]; then
  printf 'usage: %s MATERIAL_ORACLE_EXPORTER RAW_ENUM_EXPORTER\n' "$0" >&2
  exit 2
fi
ORACLE="$(realpath "$1")"
CANDIDATE="$(realpath "$2")"
OUT="${ENUM_LAYOUT_OUT:-$ROOT/scratch/enum-layouts}"
mkdir -p "$OUT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export PATH="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/bin:$PATH"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sha256sum "$ORACLE" "$CANDIDATE" > "$OUT/binaries.sha256"
for version in oracle candidate; do
  binary="$CANDIDATE"
  [[ "$version" != oracle ]] || binary="$ORACLE"
  LEAN_MIRI_LAYOUT_QUERY_TRACE=1 "$binary" --output "$OUT/$version.json" \
    --root enum_layouts -- tests/repro/compiler-queries/enum-layouts.rs \
    --crate-type=lib --crate-name=enum_layouts -Zmir-opt-level=0 \
    > "$OUT/$version.stdout" 2> "$OUT/$version.trace"
done
"$CANDIDATE" --output "$OUT/base.json" --root enum_base -- \
  tests/repro/compiler-queries/enum-layouts.rs --crate-type=lib \
  --crate-name=enum_layouts -Zmir-opt-level=0 \
  > "$OUT/base.stdout" 2> "$OUT/base.trace"
if [[ "${ENUM_LAYOUT_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.RuntimeMetadata
fi
lake env lean --run tests/compiler_queries/EnumLayoutCalculator.lean "$OUT/oracle.json"
lake env lean --run tests/compiler_queries/EnumLayouts.lean \
  "$OUT/oracle.json" "$OUT/candidate.json" "$OUT/base.json"
python3 - "$OUT" <<'PY'
import json,pathlib,re,sys
out=pathlib.Path(sys.argv[1])
candidate=json.loads((out/'candidate.json').read_text())
trace=[re.sub(r'(?<=[0-9])_usize', '', line)
       for line in (out/'candidate.trace').read_text().splitlines()]
recipes=[row for row in candidate['layout_values'] if 'enum_type' in row]
assert len(recipes)>=20, 'raw enum recipes absent'
for recipe in recipes:
    node=candidate['types'][recipe['enum_type']]
    # Debug spelling is used only to inspect explicit call-site diagnostics;
    # the Lean layout oracle compares complete typed physical identities.
    expected='lean_miri_layout_call route=canonical queried=false type='+node['display']
    assert expected in trace, ('raw enum called material layout query',node['display'])
print('raw enum explicit layout-query suppression PASS',len(recipes))
PY
