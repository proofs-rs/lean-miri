#!/usr/bin/env python3
"""Probe the patched driver using the exact stage0 compiler that built its metadata."""
import argparse, hashlib, json, os, subprocess
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,required=True)
p.add_argument('--attempt',type=int,required=True)
p.add_argument('--toolchain-root',type=Path)
p.add_argument('--representation-keys',action='store_true',help='Verify exact mask/provenance key representation and counterexamples')
p.add_argument('--stdlib-attempt',type=int,help='Successful library build supplying unchanged matching target std')
p.add_argument('--target-sysroot',type=Path,help='Preserved matching target sysroot, verified against that library attempt')
p.add_argument('--target-stdlib',action='store_true',help='Require matching stage1 library artifacts and use an ordinary std target')
a=p.parse_args();root=a.root.resolve();here=Path(__file__).resolve().parent
prepared=json.loads((root/'prepared.json').read_text())
pin=a.toolchain_root or (Path(prepared['toolchain_root']) if 'toolchain_root' in prepared else None)
assert pin is not None,'Pass the original exact --toolchain-root recorded for this build'
pin=pin.resolve();tag=f'attempt{a.attempt}-host-accessor'+('-std' if a.target_stdlib else '')+('-repr' if a.representation_keys else '');logs=root/'logs'
sha=lambda q:hashlib.file_digest(q.open('rb'),'sha256').hexdigest()
result_path=logs/(('' if a.attempt==1 else f'attempt{a.attempt}-')+'stage1-result.json')
result=json.loads(result_path.read_text())
assert result['attempt']==a.attempt and result['exit_code']==0 and result['stop_reason'] is None
assert result.get('source_audit_valid') is True,'Missing/failed protected source audit'
protected_path=root/'protected-source.json';assert sha(protected_path)==result['protected_source_manifest_sha256']
for relative,e in json.loads(protected_path.read_text()).items():
 q=root/'source'/relative;assert sha(q)==e['sha256'] and e['marker'] in q.read_text(),'Protected source changed'
compilers=sorted({q.resolve() for q in (root/'build').glob('*/stage1/bin/rustc')});assert len(compilers)==1
stage=compilers[0].parent.parent;base=stage.parent;deps=base/'stage0-sysroot/lib/rustlib/x86_64-unknown-linux-gnu/lib'
def fresh(candidates,pattern):
 hashes={sha(q) for q in (base/'stage1-rustc').rglob(pattern)};assert hashes,pattern
 matches=[q for q in candidates if sha(q) in hashes];assert len(matches)==1,(pattern,matches)
 return matches[0]
metadata={name:fresh(list(deps.glob('lib'+name+'-*.rmeta')),'lib'+name+'-*.rmeta') for name in ['rustc_driver','rustc_middle','rustc_interface','rustc_hir']}
if a.representation_keys:metadata['rustc_abi']=fresh(list(deps.glob('librustc_abi-*.rmeta')),'librustc_abi-*.rmeta')
probe_source=here/('representation-probe.rs' if a.representation_keys else 'probe.rs')
driver=fresh(list((stage/'lib').glob('librustc_driver-*.so')),'librustc_driver-*.so')
std_candidates=list((pin/'lib/rustlib/x86_64-unknown-linux-gnu/lib').glob('libstd-*.rmeta'));assert len(std_candidates)==1
std=std_candidates[0];std_so=std.with_suffix('.so');assert sha(deps/std.name)==sha(std) and std_so.is_file()
matching_std={};stdlib_result_sha=None;stdlib_anchor_sha=None
target_sysroot=(a.target_sysroot.resolve() if a.target_sysroot else stage)
if a.target_stdlib:
 library_attempt=a.stdlib_attempt or a.attempt
 library_result_path=logs/(('' if library_attempt==1 else f'attempt{library_attempt}-')+'stage1-result.json')
 library_result=json.loads(library_result_path.read_text())
 assert library_result['attempt']==library_attempt and library_result['exit_code']==0 and library_result['stop_reason'] is None and library_result.get('source_audit_valid') is True and library_result.get('build_target')=='library'
 stdlib_result_sha=sha(library_result_path)
 expected={}
 if library_attempt!=a.attempt:
  anchor_path=logs/f'attempt{library_attempt}-host-accessor-std-manifest.json'
  anchor=json.loads(anchor_path.read_text());assert anchor['result']=='PASS' and anchor['matching_target_std_hashes']
  expected={Path(path).name:digest for path,digest in anchor['matching_target_std_hashes'].items()};stdlib_anchor_sha=sha(anchor_path)
 target_lib=target_sysroot/'lib/rustlib/x86_64-unknown-linux-gnu/lib'
 for name in ['core','alloc','std','compiler_builtins']:
  installed=[q for q in target_lib.glob('lib'+name+'-*') if q.suffix in ['.rlib','.rmeta','.so']]
  assert installed,('Target library absent',name)
  for q in installed:
   assert any(sha(g)==sha(q) for g in (base/'stage1-std').rglob(q.name)),('Target std metadata stale',q)
   if expected:assert expected.get(q.name)==sha(q),('Preserved std differs from successful library attempt',q)
   matching_std[str(q)]=sha(q)
else:assert a.stdlib_attempt is None and a.target_sysroot is None,'Target std options require --target-stdlib'
binary=root/(tag+'-probe');paths={name:logs/(tag+'-'+name) for name in ['version.log','build.log','ldd.log','run.log','manifest.json']}
assert not binary.exists() and not any(q.exists() for q in paths.values()),'Refusing existing probe evidence'
env=dict(os.environ,LD_LIBRARY_PATH=':'.join(map(str,[stage/'lib',deps,base/'ci-llvm/lib',pin/'lib'])),LEAN_MIRI_OBSERVE_CTFE_ROOT='1')
version=subprocess.run([str(pin/'bin/rustc'),'-vV'],env=env,text=True,capture_output=True)
paths['version.log'].open('x').write(version.stdout+version.stderr)
assert version.returncode==0 and 'commit-hash: '+prepared['pin'] in version.stdout
command=[str(pin/'bin/rustc'),'--sysroot',str(base/'stage0-sysroot'),'--edition=2024',str(probe_source),'-Cprefer-dynamic','-L','dependency='+str(deps),
 '--extern','std='+str(std),'--extern','std='+str(std_so),'--extern','rustc_driver='+str(driver),
 *sum((['--extern',name+'='+str(q)] for name,q in metadata.items()),[]),'-o',str(binary)]
manifest={'attempt':a.attempt,'route':'original exact stage0 host compiler + fresh private metadata/newdriver; '+('matching stage1 std target' if a.target_stdlib else 'no_core target')+'; not stage1 private consumer',
 'compile_command':command,'build_result_sha256':sha(result_path),'protected_manifest_sha256':sha(protected_path),'matching_target_std_hashes':matching_std,'target_sysroot':str(target_sysroot) if a.target_stdlib else None,'stdlib_build_result_sha256':stdlib_result_sha,'stdlib_artifact_anchor_sha256':stdlib_anchor_sha,
 'environment':{k:env[k] for k in ['LD_LIBRARY_PATH','LEAN_MIRI_OBSERVE_CTFE_ROOT']},
 'hashes':{str(q):sha(q) for q in [pin/'bin/rustc',driver,std,std_so,*metadata.values(),probe_source,here/('probe-std.rs' if a.target_stdlib else 'probe-no-core.rs')]}}
compiled=subprocess.run(command,env=env,text=True,capture_output=True);paths['build.log'].open('x').write(compiled.stdout+compiled.stderr);manifest['compile_exit']=compiled.returncode
if compiled.returncode:
 manifest['result']='FAILED compilation';paths['manifest.json'].open('x').write(json.dumps(manifest,indent=2)+'\n');raise SystemExit('Private host compile failed; inspect build log; no stage2 fallback')
linked=subprocess.run(['ldd',str(binary)],env=env,text=True,capture_output=True);paths['ldd.log'].open('x').write(linked.stdout+linked.stderr)
assert linked.returncode==0 and str(driver) in linked.stdout,'Probe does not load the freshly rebuilt driver'
run=[str(binary),str(here/('probe-std.rs' if a.target_stdlib else 'probe-no-core.rs')),'--sysroot',str(target_sysroot if a.target_stdlib else base/'stage0-sysroot'),'--crate-name','ctfe_snapshot_no_core','--crate-type','lib','--edition=2024','--emit=metadata','-Zthreads=1','-o',str(root/(tag+'-target.rmeta'))]
observed=subprocess.run(run,env=env,text=True,capture_output=True);paths['run.log'].open('x').write(observed.stdout+observed.stderr)
pcs=[line for line in observed.stderr.splitlines() if line.startswith('ctfe_root_pc\t')]
pc_valid=(len(pcs)==10 and any('\tone\t' in line for line in pcs) and any('ANCHOR' in line for line in pcs)) if a.target_stdlib else (len(pcs)==2 and all('ANCHOR' in line for line in pcs))
passed=observed.returncode==0 and 'PASS actual patched snapshot:' in observed.stdout and pc_valid and (not a.representation_keys or 'PASS exact representation:' in observed.stdout)
manifest.update(run_command=run,run_exit=observed.returncode,binary_sha256=sha(binary),real_root_pcs=pcs,ldd_newdriver_verified=True,result='PASS' if passed else 'FAILED runtime')
paths['manifest.json'].open('x').write(json.dumps(manifest,indent=2)+'\n')
print(observed.stdout+observed.stderr);print(json.dumps({'result':manifest['result'],'manifest':str(paths['manifest.json'])}))
if not passed:raise SystemExit(1)
