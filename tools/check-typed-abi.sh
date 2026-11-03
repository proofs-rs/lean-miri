#!/usr/bin/env bash
# Experimental ABI transport: retained fixtures are adapted, never called fresh
# Rust/Miri executions, and no reference sidecars are fabricated for adapters.
set -euo pipefail
cd "$(dirname "$0")/.."
export ELAN_HOME="${LEAN_MIRI_ELAN_HOME:-$PWD/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
bash tools/build-exporter.sh --bin prepare-abi-snapshot
flock --no-fork /tmp/lean-miri-lake-build.lock lake build typed_abi_wire_tests
python3 tests/input/build_id_fixtures.py
mkdir -p scratch/typed-abi-tests
for name in genuine-mir-features genuine-fresh; do
  exporter/target/release/prepare-abi-snapshot \
    "scratch/decoder-id-inputs/$name.json" "scratch/typed-abi-tests/$name.json"
  .lake/build/bin/typed_abi_wire_tests "scratch/typed-abi-tests/$name.json" --full
done
python3 - <<'PY'
import copy,json
from pathlib import Path
base=Path('scratch/typed-abi-tests/genuine-mir-features.json')
with base.open() as stream: original=json.load(stream)
index=next(i for i,node in enumerate(original['shared_payloads']['nodes'])
           if isinstance(node,dict) and '$lean_miri_abi_arg' in node)
for name,slot,value in [('missing-cast-fields',2,{'kind':'Cast'}),
                        ('dangling-argument-type',0,10**30),
                        ('malformed-layout',1,{'status':'supported'})]:
    document=copy.deepcopy(original)
    document['shared_payloads']['nodes'][index]['$lean_miri_abi_arg'][slot]=value
    (base.parent/(name+'.json')).write_text(json.dumps(document,separators=(',',':')))
PY
for name in missing-cast-fields dangling-argument-type malformed-layout; do
  .lake/build/bin/typed_abi_wire_tests "scratch/typed-abi-tests/$name.json" --full
done
python3 - <<'PY'
import json,sys
from pathlib import Path
sys.path.insert(0,'tools')
from mir_json import unpack_typed_abi_nodes
for path in Path('scratch/typed-abi-tests').glob('genuine-*.json'):
    with path.open() as stream: packed=json.load(stream)
    with (Path('scratch/decoder-id-inputs')/path.name).open() as stream: original=json.load(stream)
    catalog=packed['shared_payloads']
    catalog['nodes']=unpack_typed_abi_nodes(catalog['nodes'],catalog)
    del catalog['typed_abi_version']
    assert packed==original,path
    print(path.name,': exact complete DAG/source round-trip PASS')
PY
python3 -m unittest discover -s exporter/tests -p test_mir_json.py
