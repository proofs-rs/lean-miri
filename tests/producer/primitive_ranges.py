#!/usr/bin/env python3
"""Lossless actual rustc u128/niche metadata and strict decoder boundary tests.
Finite producer/adapter checks; no Rust safety theorem.
"""
from pathlib import Path
import json, os, subprocess, sys
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_document

work=ROOT/'scratch/primitive-ranges-qa';work.mkdir(parents=True,exist_ok=True)
toolchain=ROOT/'.rustup/toolchains/miri-exporter-8144389c895d'
env={**os.environ,'ELAN_HOME':str(ROOT/'.elan'),'MIRI_SYSROOT':str(ROOT/'scratch/miri-sysroot'),'LD_LIBRARY_PATH':str(toolchain/'lib')}
env['PATH']=str(toolchain/'bin')+':'+env.get('PATH','')
output=work/'actual.json'
subprocess.run([str(ROOT/'exporter/target/debug/lean-miri-mir-exporter'),'--output',str(output),'tests/producer/primitive_ranges.rs','--crate-type=lib','--crate-name=primitive_ranges'],cwd=ROOT,env=env,check=True)
document=load_mir_document(output);lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
for source in ['rustc','miri']:assert document['producer'][source+'_commit']==lock['pins'][source]['commit']
type_id=document['compiler_runtime_primitives']['u128']['type_id']
node=next(t for t in document['types'] if t['type_id']==type_id)
assert node['layout']['backend_repr']['scalar']['valid_range']=={'start':'0','end':str(2**128-1)}
assert any(t.get('layout',{}).get('largest_niche',{}).get('valid_range',{}).get('end')==str(2**128-1) for t in document['types'] if t.get('layout',{}).get('largest_niche'))
subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/producer/PrimitiveRanges.lean',str(output)],cwd=ROOT,env=env,check=True)
