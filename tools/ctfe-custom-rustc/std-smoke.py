#!/usr/bin/env python3
"""Compile, link and execute a std fixture with the verified matching stage1 sysroot."""
import argparse, hashlib, json, os, subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,required=True)
p.add_argument('--attempt',type=int,required=True)
a=p.parse_args();root=a.root.resolve();here=Path(__file__).resolve().parent;logs=root/'logs';tag=f'attempt{a.attempt}-std-smoke'
sha=lambda q:hashlib.file_digest(q.open('rb'),'sha256').hexdigest()
probe_manifest=logs/f'attempt{a.attempt}-host-accessor-std-manifest.json';probe=json.loads(probe_manifest.read_text())
assert probe['result']=='PASS' and probe['attempt']==a.attempt and probe['matching_target_std_hashes']
assert sha(root/'protected-source.json')==probe['protected_manifest_sha256']
for relative,e in json.loads((root/'protected-source.json').read_text()).items():
 q=root/'source'/relative;assert sha(q)==e['sha256'] and e['marker'] in q.read_text()
for path,digest in probe['matching_target_std_hashes'].items():assert sha(Path(path))==digest,'Matching target std changed'
stages=sorted({q.resolve().parent.parent for q in (root/'build').glob('*/stage1/bin/rustc')});assert len(stages)==1
stage=stages[0];source=here/'probe-std-codegen.rs';binary=root/tag
paths={name:logs/(tag+'-'+name) for name in ['build.log','run.log','manifest.json']}
assert not binary.exists() and not any(q.exists() for q in paths.values()),'Refusing existing smoke evidence'
env=dict(os.environ,LD_LIBRARY_PATH=str(stage/'lib'),TMPDIR=str(root/'tmp'))
target_sysroot=Path(probe.get('target_sysroot') or stage)
command=[str(stage/'bin/rustc'),'--sysroot',str(target_sysroot),'--edition=2024','--crate-name','ctfe_matching_std_smoke',str(source),'-C','linker='+str(root/'linker-single-thread.sh'),'-o',str(binary)]
built=subprocess.run(command,env=env,text=True,capture_output=True);paths['build.log'].open('x').write(built.stdout+built.stderr)
manifest={'attempt':a.attempt,'command':command,'environment':{k:env[k] for k in ['LD_LIBRARY_PATH','TMPDIR']},'matching_std_probe_manifest_sha256':sha(probe_manifest),'compile_exit':built.returncode,'compiler_sha256':sha(stage/'bin/rustc'),'source_sha256':sha(source),'stage2_started':False}
if built.returncode:
 manifest['result']='FAILED compilation';paths['manifest.json'].open('x').write(json.dumps(manifest,indent=2)+'\n');raise SystemExit(1)
run=subprocess.run([str(binary)],env=env,text=True,capture_output=True);paths['run.log'].open('x').write(run.stdout+run.stderr)
passed=run.returncode==0 and run.stdout=='PASS matching stage1 std Vec/iterator/codegen execution\n'
manifest.update(run_exit=run.returncode,binary_sha256=sha(binary),result='PASS' if passed else 'FAILED runtime')
paths['manifest.json'].open('x').write(json.dumps(manifest,indent=2)+'\n');print(run.stdout+run.stderr);print(json.dumps({'result':manifest['result'],'manifest':str(paths['manifest.json'])}))
if not passed:raise SystemExit(1)
