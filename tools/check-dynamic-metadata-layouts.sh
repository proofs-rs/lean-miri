#!/usr/bin/env bash
# Complete rustc layout comparisons from raw DynMetadata source in empty Worlds.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
if [[ $# != 2 ]]; then
  printf 'usage: %s FROZEN_ORACLE_JSON SOURCE_EXPORTER\n' "$0" >&2
  exit 2
fi
ORACLE="$(realpath "$1")"
CANDIDATE="$(realpath "$2")"
OUT="${DYNAMIC_METADATA_OUT:-$ROOT/scratch/dynamic-metadata-layouts}"
mkdir -p "$OUT"
export RUSTUP_HOME="${RUSTUP_HOME:-$ROOT/.rustup}"
export MIRI_SYSROOT="${MIRI_SYSROOT:-$ROOT/scratch/miri-sysroot}"
export PATH="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/bin:$PATH"
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/miri-exporter-8144389c895d/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
sha256sum "$ORACLE" "$CANDIDATE" > "$OUT/inputs.sha256"
for root in enum_layouts enum_base; do
  output=candidate
  [[ "$root" != enum_base ]] || output=base
  LEAN_MIRI_LAYOUT_QUERY_TRACE=1 "$CANDIDATE" --output "$OUT/$output.json" \
    --root "$root" -- tests/repro/compiler-queries/univariant-enum-layouts.rs \
    --crate-type=lib --crate-name=univariant_enums -Zmir-opt-level=0 \
    > "$OUT/$output.stdout" 2> "$OUT/$output.trace"
done
python3 - "$OUT" <<'PYCODE'
import json,pathlib,re,sys
out=pathlib.Path(sys.argv[1]); source=json.loads((out/'candidate.json').read_text())
trace=(out/'candidate.trace').read_text(); enums=0; pointers=0
for node in source['types']:
    shape=node['shape']; recipe=source['layout_values'][source['layouts'][node['layout']]]
    if node['display'] in ['DynamicControl','NestedDynamicControl']:
        assert recipe.get('enum_type')==node['type_id'], 'covered dynamic enum retained a layout answer'
        enums+=1
    elif shape['kind'] in ['reference','raw_pointer'] and source['types'][shape['pointee']]['shape']['kind']=='dynamic_trait_object':
        assert recipe.get('pointer_type')==node['type_id'], 'covered fat pointer retained a layout answer'
        pointers+=1
    else:
        continue
    if node['display'] in ['DynamicControl','NestedDynamicControl']:
        expected='lean_miri_layout_call route=canonical queried=false type='+node['display']
        assert expected in trace, ('source layout still acquired canonical answer',node['display'])
assert enums==2 and pointers>=1, 'source metadata layout query coverage missing'
# Traces print rustc Debug; TypeNode.display uses the diagnostic type printer.
# Check every canonical request for a dyn pointer, including residual requests.
events=re.findall(r'^lean_miri_layout_call route=(canonical(?:-residual)?) queried=(true|false) type=(.*)$',trace,re.M)
fat=[event for event in events if re.match(r'^(?:&|\*(?:const|mut)\s).*\bdyn\b',event[2])]
assert len(fat)>=pointers and all(route=='canonical' and queried=='false' for route,queried,_ in fat), 'canonical dyn pointer layout acquisition remains'
for node in source['types']:
    if node['shape']['kind']=='dynamic_trait_object':
        assert node['compiler_facts']['type_queries'].get('pointer_metadata_type') is None
print('PASS explicit layout-query suppression',enums,'dynamic enums and',pointers,'fat pointers')
PYCODE
if [[ "${DYNAMIC_METADATA_SKIP_BUILD:-0}" != 1 ]]; then
  flock /tmp/lean-miri-lake-build.lock lake build Miri.Input.Decoder Miri.Input.RuntimeMetadata
fi
lake env lean --run tests/compiler_queries/DynamicMetadataLayouts.lean \
  "$ORACLE" "$OUT/candidate.json" "$OUT/base.json"
