#!/usr/bin/env python3
"""Exercise canonical metadata on actual pinned compiler query results."""
import os
import json
from pathlib import Path
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_document
env=dict(os.environ, ELAN_HOME=str(ROOT/'.elan'), MIRI_SYSROOT=str(ROOT/'scratch/miri-sysroot'))
toolchain=ROOT/'.rustup/toolchains/miri-exporter-8144389c895d'
env['PATH']=str(toolchain/'bin')+':'+env.get('PATH','')
env['LD_LIBRARY_PATH']=str(toolchain/'lib')+(':'+env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
with tempfile.TemporaryDirectory(prefix='runtime-metadata-') as tmp:
    output=Path(tmp)/'metadata.json'
    subprocess.run([str(ROOT/'exporter/target/debug/lean-miri-mir-exporter'),'--output',str(output),'--root','records',str(ROOT/'tests/runtime_metadata/fixture.rs'),'--crate-type=lib','--crate-name=runtime_metadata'],cwd=ROOT,env=env,check=True)
    lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
    document=load_mir_document(output)
    assert document['producer']['rustc_commit']==lock['pins']['rustc']['commit']
    assert document['producer']['miri_commit']==lock['pins']['miri']['commit']
    subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/runtime_metadata/RuntimeMetadata.lean',str(output)],cwd=ROOT,env=env,check=True)
    subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/runtime_metadata/StrFieldProjection.lean'],cwd=ROOT,env=env,check=True)
