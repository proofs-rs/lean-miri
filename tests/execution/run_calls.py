#!/usr/bin/env python3
"""Actual exported MIR integration and pinned Miri observation comparison.

Finite single-thread integer observations; not a UB-freedom proof.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'tools'))
from mir_json import load_mir_document
TOOLCHAIN = ROOT/'.rustup/toolchains/miri-exporter-8144389c895d'
MIRI = ROOT/'upstream/miri-source/target/debug/miri'
SYSROOT = ROOT/'scratch/miri-sysroot'

def main():
    env = dict(os.environ, ELAN_HOME=str(ROOT/'.elan'), RUSTUP_HOME=str(ROOT/'.rustup'), CARGO_HOME=str(ROOT/'.cargo'), MIRI_SYSROOT=str(SYSROOT))
    env['PATH'] = str(TOOLCHAIN/'bin')+':'+str(ROOT/'.cargo/bin')+':'+env.get('PATH','')
    env['LD_LIBRARY_PATH'] = str(TOOLCHAIN/'lib')+(':'+env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
    build = json.loads((ROOT/'scratch/miri-reference-build.json').read_text())
    assert hashlib.sha256(MIRI.read_bytes()).hexdigest() == build['binary_sha256'], 'pinned Miri binary changed'
    lock = json.loads((ROOT/'upstream/source-lock.json').read_text())
    source = ROOT/'tests/execution/fixture_calls.rs'
    with tempfile.TemporaryDirectory(prefix='lean-miri-execution-') as temporary:
        tmp = Path(temporary)
        exported = tmp/'selected.json'
        subprocess.run([str(ROOT/'exporter/target/debug/lean-miri-mir-exporter'),'--output',str(exported),'--root','root','--root','tail_root','--root','overflow_root',str(source),'--crate-type=lib','--crate-name=fixture_calls'],cwd=ROOT,env=env,check=True)
        document = load_mir_document(exported)
        assert document['producer']['rustc_commit'] == lock['pins']['rustc']['commit']
        assert document['producer']['miri_commit'] == lock['pins']['miri']['commit']
        assert build['rustc_commit'] == lock['pins']['rustc']['commit']
        module = tmp/'tests/execution/ReturnMemory.olean'
        module.parent.mkdir(parents=True)
        subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','-o',str(module),'tests/execution/ReturnMemory.lean'],cwd=ROOT,env=env,check=True)
        basepath = subprocess.check_output([str(ROOT/'.elan/bin/lake'),'env','printenv','LEAN_PATH'],cwd=ROOT,env=env,text=True).strip()
        env['LEAN_PATH'] = str(tmp)+':'+basepath
        lean = subprocess.run([str(ROOT/'.elan/bin/lake'),'env','lean','--run','tests/execution/ImportedCalls.lean',str(exported)],cwd=ROOT,env=env,text=True,capture_output=True)
        assert lean.returncode == 0, lean.stdout+lean.stderr
        lines = lean.stdout.splitlines()
        assert 'nested=42' in lines and 'tail=42' in lines and 'callee_overflow=panic' in lines, lean.stdout
        for function,argument,expected in [('root',41,'nested=42'),('tail_root',41,'tail=42'),('overflow_root',4294967295,'callee_overflow=panic')]:
            wrapper = tmp/f'case_{function}.rs'
            # Both export and reference compile the same original Rust source.
            wrapper.write_text(f'#![feature(explicit_tail_calls)]\n#[path = {json.dumps(str(source))}] mod fixture;\nfn main() {{ let value = std::hint::black_box({argument}u32); println!("{{}}", fixture::{function}(value)); }}\n')
            reference = subprocess.run([str(MIRI),'--sysroot',str(SYSROOT),'--edition=2021','-C','overflow-checks=on','-Zmiri-tree-borrows','-Zmiri-seed=0',str(wrapper)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)
            if argument == 41:
                assert reference.returncode == 0 and reference.stdout.strip() == '42', (reference.stdout,reference.stderr)
            else:
                assert reference.returncode != 0 and 'panicked at' in reference.stderr and 'attempt to add with overflow' in reference.stderr, reference.stderr
                assert 'Undefined Behavior' not in reference.stderr, reference.stderr
            assert expected in lines
            print(f'pinned Miri / exported-MIR Lean agree: {expected}')
        print(lean.stdout.strip())

if __name__ == '__main__':
    main()
