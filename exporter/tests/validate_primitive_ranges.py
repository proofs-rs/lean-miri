#!/usr/bin/env python3
"""Check actual compiler u128/niche metadata without invoking Lean."""
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_document

output=Path(sys.argv[1])
document=load_mir_document(output);lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
for source in ['rustc','miri']:assert document['producer'][source+'_commit']==lock['pins'][source]['commit']
type_id=document['compiler_runtime_primitives']['u128']['type_id']
node=next(t for t in document['types'] if t['type_id']==type_id)
assert node['layout']['backend_repr']['scalar']['valid_range']=={'start':'0','end':str(2**128-1)}
assert any(t.get('layout',{}).get('largest_niche',{}).get('valid_range',{}).get('end')==str(2**128-1) for t in document['types'] if t.get('layout',{}).get('largest_niche'))
print('validated exact compiler u128 range and niche metadata')
