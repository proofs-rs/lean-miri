#!/usr/bin/env python3
"""Check source u128 constructor and exact niche material without invoking Lean."""
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

output=Path(sys.argv[1])
document=load_mir_document(output);lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
for source in ['rustc','miri']:assert document['producer'][source+'_commit']==lock['pins'][source]['commit']
type_id=document['compiler_runtime_primitives']['u128']
node=next(t for t in document['types'] if t['type_id']==type_id)
assert node['shape'] == {'kind': 'uint', 'unsigned_kind': 'u128'}
assert pool_entry(document, 'layouts', node['layout']) == {'primitive_recipe': 'u128'}
assert any(layout.get('largest_niche', {}).get('valid_range', {}).get('end') == str(2**128-1) for layout in document['layouts'] if layout.get('largest_niche'))
print('validated u128 material constructor and exact compiler niche range; Lean checks the computed primitive range')
