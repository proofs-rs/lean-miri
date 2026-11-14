#!/usr/bin/env python3
"""Coordinator-only stage1 attempt; stop on reserve/cap/oom events, never clean."""
import argparse,hashlib,json,os,shutil,signal,subprocess,time
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True);parser.add_argument('--toolchain-root',type=Path);parser.add_argument('--build-target',choices=['compiler/rustc','library'],default='compiler/rustc');parser.add_argument('--attempt',type=int,default=1);parser.add_argument('--initial-headroom-bytes',type=int,default=1_500_000_000);parser.add_argument('--build-cap-bytes',type=int,default=3_000_000_000);parser.add_argument('--reserve-bytes',type=int,default=800_000_000);args=parser.parse_args()
root=args.root.resolve();assert (root/'prepared.json').is_file();source=root/'source';build=root/'build';logs=root/'logs';start_free=shutil.disk_usage(root).free
if args.attempt<1:raise SystemExit('attempt must be positive')
prefix='' if args.attempt==1 else f'attempt{args.attempt}-'
log_paths={name:logs/(prefix+name) for name in ['preflight-resources.json','stage1.log','resources.jsonl','stage1-result.json','source-audit-before.json','source-audit-after.json']}
existing=[str(path) for path in log_paths.values() if path.exists()]
if existing:raise SystemExit('Refusing to overwrite attempt evidence: '+', '.join(existing))
if args.initial_headroom_bytes<0:raise SystemExit('initial headroom must be nonnegative')
if start_free < args.reserve_bytes+args.initial_headroom_bytes:raise SystemExit('Insufficient initial build headroom; no cleanup attempted')
protected_path=root/'protected-source.json'
assert protected_path.is_file(),'Protected repaired source manifest is required'
protected=json.loads(protected_path.read_text())
protected_sha=hashlib.sha256(protected_path.read_bytes()).hexdigest()
def audit_source():
 rows={}
 try: current_manifest=hashlib.sha256(protected_path.read_bytes()).hexdigest()
 except OSError: current_manifest=None
 for relative,expected in protected.items():
  path=source/relative
  try:
   contents=path.read_bytes();actual=hashlib.sha256(contents).hexdigest();marker=expected['marker'].encode() in contents
  except OSError: actual=None;marker=False
  rows[relative]={'sha256':actual,'marker_present':marker,'expected_sha256':expected['sha256']}
 return {'manifest_sha256':current_manifest,'valid':current_manifest==protected_sha and all(row['sha256']==row['expected_sha256'] and row['marker_present'] for row in rows.values()),'files':rows}
before_audit=audit_source()
log_paths['source-audit-before.json'].open('x').write(json.dumps(before_audit,indent=2)+'\n')
assert before_audit['valid'],'Protected source changed before build; no compiler launched'
mem=Path('/sys/fs/cgroup/memory.current');events=Path('/sys/fs/cgroup/memory.events');stat=Path('/sys/fs/cgroup/memory.stat')
def numbers():return {k:int(v) for k,v in (line.split() for line in events.read_text().splitlines())}
def memory_sample():
 current=int(mem.read_text())
 statistics={k:int(v) for k,v in (line.split() for line in stat.read_text().splitlines())}
 inactive_file=statistics['inactive_file']
 return {'memory_current':current,'memory_inactive_file':inactive_file,'memory_working_set':max(0,current-inactive_file)}
preflight=memory_sample()
log_paths['preflight-resources.json'].open('x').write(json.dumps({'time':time.time(),'free_bytes':start_free,**preflight,'memory_events':numbers(),'source_manifest_sha256':protected_sha,'CARGO_INCREMENTAL':'0'},indent=2)+'\n')
if preflight['memory_working_set']>13*1024**3:raise SystemExit('Coordinate with Lean barrier first: cgroup working set (current - inactive_file, clamped at zero) >13GiB')
initial_events=numbers();env=dict(os.environ,CARGO_NET_OFFLINE='true',CARGO_INCREMENTAL='0',CARGO_BUILD_JOBS='1',CMAKE_BUILD_PARALLEL_LEVEL='1',TMPDIR=str(root/'tmp'),CARGO_HOME=str(root/'cargo-home'))
prepared=json.loads((root/'prepared.json').read_text())
pin=args.toolchain_root or (Path(prepared['toolchain_root']) if 'toolchain_root' in prepared else None)
assert pin is not None,'Original exact --toolchain-root is required for this prepared root'
pin=pin.resolve()
env['LD_LIBRARY_PATH']=str(pin/'lib')+(':'+env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '')
command=['python3','x.py','--config',str(root/'bootstrap.toml'),'build','--stage','1',args.build_target]
reason=None
with log_paths['stage1.log'].open('x') as output,log_paths['resources.jsonl'].open('x') as resources:
 process=subprocess.Popen(command,cwd=source,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
 while process.poll() is None:
  free=shutil.disk_usage(root).free;sample=memory_sample();now_events=numbers();source_audit=audit_source();row={'time':time.time(),'free_bytes':free,'consumed_since_launch':start_free-free,**sample,'memory_events':now_events,'source_audit_valid':source_audit['valid']};resources.write(json.dumps(row)+'\n');resources.flush()
  if not source_audit['valid']:reason='protected source changed'
  elif free<args.reserve_bytes:reason='disk reserve'
  elif start_free-free>args.build_cap_bytes:reason='build byte cap'
  elif sample['memory_working_set']>15*1024**3:reason='memory working-set reserve'
  elif now_events.get('oom',0)>initial_events.get('oom',0):reason='new cgroup oom event'
  if reason:
   os.killpg(process.pid,signal.SIGINT)
   try:process.wait(timeout=20)
   except subprocess.TimeoutExpired:os.killpg(process.pid,signal.SIGTERM);process.wait()
   break
  time.sleep(2)
 after_audit=audit_source();log_paths['source-audit-after.json'].open('x').write(json.dumps(after_audit,indent=2)+'\n')
 if not after_audit['valid']:reason='protected source changed'
 result={'build_target':args.build_target,'initial_headroom_bytes':args.initial_headroom_bytes,'reserve_bytes':args.reserve_bytes,'build_cap_bytes':args.build_cap_bytes,'source_audit_valid':after_audit['valid'],'protected_source_manifest_sha256':protected_sha,'CARGO_INCREMENTAL':'0','attempt':args.attempt,'command':command,'exit_code':process.wait(),'stop_reason':reason,'free_bytes':shutil.disk_usage(root).free,'stage2_started':False};log_paths['stage1-result.json'].open('x').write(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if result['exit_code']!=0 or reason is not None:raise SystemExit(1)
print('Stage1 build completed. rustc_private metadata/accessor probe is mandatory; no success/admission inferred. Do not start stage2 automatically.')
