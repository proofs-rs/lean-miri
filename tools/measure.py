#!/usr/bin/env python3
"""Build and freeze the native runner, then measure with aligned counters.

Example:
  python3 tools/measure.py --input scratch/main.json --name small-old --runs 3
Use --executable for a frozen native binary without building. For Lean --run,
pass --runner tools/Run.lean and set LEAN_PATH to a frozen module closure. The runner and
its descendants inherit the selected CPU affinity and LEAN_NUM_THREADS=1.
The historical guest_start boundary follows negative preflight and includes
bootstrap. Post-bootstrap time includes interpretation and exit finalization;
terminal_observed accepts error/unsupported output and never certifies safety.
"""
import argparse, hashlib, json, os, pathlib, re, selectors, signal, subprocess, sys, time, resource, fcntl, shutil, tempfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'scratch/performance'
TICKS = os.sysconf('SC_CLK_TCK')
MARKERS = {
 'decode: start':'decode_start', 'decode: ready obligations=0':'decode_end',
 'lower: start':'lower_start', 'lower: complete':'lower_end',
 'prepare: start':'prepare_start', 'prepare: complete':'prepare_end',
 'run: start':'setup_start',
 'validation_mismatch:failed_before_guest_step; state and host-init snapshots unchanged':'guest_start',
}
def sha(path):
 h=hashlib.sha256()
 with open(path,'rb') as f:
  for block in iter(lambda:f.read(1<<20),b''): h.update(block)
 return h.hexdigest()
def proc_rows(pgid):
 rows=[]
 for p in pathlib.Path('/proc').iterdir():
  if not p.name.isdigit(): continue
  try:
   stat=(p/'stat').read_text(); tail=stat[stat.rfind(')')+2:].split()
   if int(tail[2]) != pgid: continue # pgrp (field 5; tail starts field 3)
   sched=(p/'schedstat').read_text().split()
   rows.append({'pid':int(p.name),'utime_ticks':int(tail[11]),'stime_ticks':int(tail[12]),'sched_runtime_ns':int(sched[0]),'sched_runqueue_ns':int(sched[1])})
  except (OSError,ValueError,IndexError): pass
 return rows
def read_file(path):
 try:return pathlib.Path(path).read_text()
 except OSError:return None
def counters(pgid, cpu_id):
 cpu=read_file('/proc/stat') or ''; steal=None
 for line in cpu.splitlines():
  if line.startswith(f'cpu{cpu_id} '):
   cols=line.split(); steal=int(cols[8]) if len(cols)>8 else None; break
 cstat=read_file('/sys/fs/cgroup/cpu.stat'); cs={}
 if cstat:
  for line in cstat.splitlines():
   k,v=line.split(); cs[k]=int(v)
 mem=read_file('/sys/fs/cgroup/memory.events'); io=read_file('/sys/fs/cgroup/io.stat'); mstat=read_file('/sys/fs/cgroup/memory.stat'); ms={}
 if mstat:
  for line in mstat.splitlines():
   k,v=line.split(); ms[k]=int(v)
 rss=0
 for row in proc_rows(pgid):
  try:
   status=pathlib.Path(f"/proc/{row['pid']}/status").read_text()
   rss += next(int(z.split()[1])*1024 for z in status.splitlines() if z.startswith('VmRSS:'))
  except (OSError,StopIteration,ValueError): pass
 nonreclaim=sum(ms.get(k,0) for k in ('anon','shmem','slab_unreclaimable','kernel_stack','pagetables','sock'))
 return {'wall_monotonic_ns':time.monotonic_ns(),'process_group_rss_bytes':rss,'cgroup_nonreclaim_bytes':nonreclaim,'cgroup_memory_stat':ms,'selected_cpu_steal_ticks':steal,'processes':proc_rows(pgid),'cgroup_cpu_stat':cs,'memory_events':mem,'io_stat':io,'cpu_max':read_file('/sys/fs/cgroup/cpu.max'),'cpu_psi':read_file('/proc/pressure/cpu'),'cgroup_cpu_psi':read_file('/sys/fs/cgroup/cpu.pressure')}
def build_native_snapshot(output, env):
 # Match run.sh's build lock and target. Freeze under that same lock
 # so another Lake writer cannot replace the measured binary between trials.
 with tempfile.NamedTemporaryFile(prefix='native-build-',suffix='.log',dir=output,delete=False) as log:
  logpath=pathlib.Path(log.name)
  with open('/tmp/lean-miri-lake-build.lock','a') as lock:
   fcntl.flock(lock,fcntl.LOCK_EX)
   built=subprocess.run([str(ROOT/'.elan/bin/lake'),'build','native_runner'],cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
   if built.returncode:
    raise SystemExit(f'Runner build failed; log: {logpath}')
   frozen=pathlib.Path(tempfile.mkdtemp(prefix='native-artifacts-',dir=output))/'native_runner'
   shutil.copy2(ROOT/'.lake/build/bin/native_runner',frozen)
 return frozen,logpath

def main():
 global OUT
 ap=argparse.ArgumentParser(); ap.add_argument('--input',required=True); ap.add_argument('--name',required=True); entry=ap.add_mutually_exclusive_group(); entry.add_argument('--runner',help='explicit Lean --run entry; requires --lean-path'); entry.add_argument('--executable',help='run a frozen native executable instead of Lean --run'); ap.add_argument('--runs',type=int,default=3); ap.add_argument('--cpu',type=int,default=2); ap.add_argument('--timeout',type=int,default=900); ap.add_argument('--lean-path',default=os.environ.get('LEAN_PATH')); ap.add_argument('--output-dir', default=str(OUT)); ap.add_argument('--seed',type=int,help='bounded diagnostic u64 seed, passed to the runner'); ap.add_argument('--profile',action='store_true',help='enable internal profiles in the runner'); a=ap.parse_args(); OUT=pathlib.Path(a.output_dir).resolve(); OUT.mkdir(parents=True, exist_ok=True)
 if a.seed is not None and not 0 <= a.seed < 2**64: ap.error('--seed must be an unsigned u64')
 inp=pathlib.Path(a.input); inp=inp if inp.is_absolute() else ROOT/inp
 env=os.environ.copy(); env.update({'ELAN_HOME':str(ROOT/'.elan'),'LEAN_NUM_THREADS':'1'})
 if a.lean_path: env['LEAN_PATH']=a.lean_path
 buildlog=None
 if a.runner:
  if not a.lean_path: raise SystemExit('LEAN_PATH must point to an immutable module closure')
  runner=pathlib.Path(a.runner); runner=runner if runner.is_absolute() else ROOT/runner
  command=['taskset','-c',str(a.cpu),str(ROOT/'.elan/bin/lean'),'--run',str(runner),str(inp)]
 else:
  if a.executable:
   runner=pathlib.Path(a.executable); runner=runner if runner.is_absolute() else ROOT/runner
  else:
   runner,buildlog=build_native_snapshot(OUT,env)
  command=['taskset','-c',str(a.cpu),str(runner),str(inp)]
 if a.seed is not None: command.extend(['--seed',str(a.seed)])
 if a.profile: command.append('--profile')
 result={'name':a.name,'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'command':command,'cwd':str(ROOT),'input':str(inp),'input_bytes':inp.stat().st_size,'input_sha256':sha(inp),'runner_sha256':sha(runner),'collector_sha256':sha(pathlib.Path(__file__)),'collector_version':'runner-7','execution_mode':'lean-run' if a.runner else 'native','build_log':str(buildlog) if buildlog else None,'profile_requested':a.profile,'diagnostic_seed':a.seed,'lean_path':a.lean_path,'cpu':a.cpu,'lean_num_threads':1,'clock_ticks_per_second':TICKS,'cpu_max':read_file('/sys/fs/cgroup/cpu.max'),'psi_available':{'host_proc':read_file('/proc/pressure/cpu') is not None,'cgroup':read_file('/sys/fs/cgroup/cpu.pressure') is not None},'runs':[],'guards':{'wall_seconds':a.timeout,'process_group_rss_bytes':12000000000,'cgroup_nonreclaim_bytes':14000000000,'sample_interval_seconds':2,'term_grace_seconds':5}}
 spans={'read_decode':('decode_start','decode_end'),'lower':('lower_start','lower_end'),'prepare':('prepare_start','prepare_end'),'setup_preflight':('setup_start','guest_start'),'bootstrap_setup':('guest_start','bootstrap_ready'),'post_bootstrap_to_candidate0':('bootstrap_ready','guest_end'),'guest_to_candidate0':('guest_start','guest_end')}
 spans.update({'post_bootstrap_to_raw_result':('bootstrap_ready','raw_result'),'finalization':('finalization_start','finalization_end'),'leak_check':('leak_check_start','leak_check_end'),'leak_walk':('leak_walk_start','leak_walk_end')})
 for i in range(1,a.runs+1):
  run={'number':i,'events':{},'snapshots':{},'markers':[],'samples':[],'internal_profile_spans':[]}; start=time.monotonic_ns(); rusage_before=resource.getrusage(resource.RUSAGE_CHILDREN)
  logpath=OUT/f'{a.name}-{i:02d}.log'
  with logpath.open('xb') as log:
   child=subprocess.Popen(command,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
   pgid=child.pid; run['start_counters']=counters(pgid,a.cpu); sel=selectors.DefaultSelector(); sel.register(child.stdout,selectors.EVENT_READ); buf=b''; deadline=time.monotonic()+a.timeout; next_sample=time.monotonic(); stop_reason=None; term_at=None
   while sel.get_map() or child.poll() is None:
    nowwall=time.monotonic()
    if nowwall>=next_sample:
     sample=counters(pgid,a.cpu); sample['seconds']=time.monotonic_ns()/1e9-run['start_counters']['wall_monotonic_ns']/1e9; run['samples'].append(sample); next_sample=nowwall+2
     if stop_reason is None and child.poll() is None:
      if nowwall>=deadline: stop_reason='wall guard'
      elif sample['process_group_rss_bytes']>=12000000000: stop_reason='process-group RSS guard'
      elif sample['cgroup_nonreclaim_bytes']>=14000000000: stop_reason='cgroup nonreclaim memory guard'
      if stop_reason is not None:
       run['stop_reason']=stop_reason; term_at=nowwall; os.killpg(pgid,signal.SIGTERM)
     elif term_at is not None and child.poll() is None and nowwall-term_at>=5:
      run['sigkill_after_grace']=True; os.killpg(pgid,signal.SIGKILL); term_at=None
    for key,_ in sel.select(.2):
     chunk=os.read(key.fd,65536)
     if not chunk: sel.unregister(key.fileobj); continue
     log.write(chunk); log.flush(); buf+=chunk
     while b'\n' in buf:
      raw,buf=buf.split(b'\n',1); s=raw.decode(errors='replace').rstrip('\r'); now=time.monotonic_ns();
      prof=re.match(r'^(decoder|preparation|prepare|startup|finalization|execution)\.(\S+) took ([0-9.]+)(ms|s)$',s)
      if prof:
       value=float(prof.group(3)); seconds=value/1000 if prof.group(4)=='ms' else value
       run['internal_profile_spans'].append({'provider':prof.group(1),'name':prof.group(2),'seconds':seconds,'reported':s,'wall_monotonic_ns':now})
       if prof.group(1)=='startup' and prof.group(2)=='bootstrap_ready' and 'bootstrap_ready' not in run['events'] and 'guest_end' not in run['events']:
        run['events']['bootstrap_ready']=now; run['snapshots']['bootstrap_ready']=counters(pgid,a.cpu); run['markers'].append('startup.bootstrap_ready')
       if prof.group(1)=='finalization' and 'guest_end' not in run['events']:
        name=prof.group(2)
        event={'start':'finalization_start','complete':'finalization_end','leak_check.start':'leak_check_start','leak_check.complete':'leak_check_end','leak_walk.complete':'leak_walk_end'}.get(name)
        if name.startswith('raw_result.'):
         event='raw_result'
         if event not in run['events']: run['raw_result_kind']=name.removeprefix('raw_result.')
        if name.startswith('leak_walk.start.'):
         event='leak_walk_start'
         if event not in run['events']: run['leak_walk_shape']=name.removeprefix('leak_walk.start.')
        if event and event not in run['events']:
         run['events'][event]=now; run['snapshots'][event]=counters(pgid,a.cpu); run['markers'].append('finalization.'+name)
      if s in MARKERS:
       k=MARKERS[s]; run['events'][k]=now; run['snapshots'][k]=counters(pgid,a.cpu); run['markers'].append(s)
      if s.startswith('candidate=0:'):
       run['events']['guest_end']=now; run['snapshots']['guest_end']=counters(pgid,a.cpu); run['candidate0']=s
      if s.startswith('run: finalized_exit') or s.startswith('run: undefined_behavior ') or s.startswith('run: unsupported ') or s.startswith('run: failed ') or s.startswith('run: pending '):
       run['events']['output_end']=now; run['snapshots']['output_end']=counters(pgid,a.cpu); run['terminal_line']=s
      if s.startswith('decode: ready obligations='):
       run['readiness_line']=s
      if s.startswith('preparation_only: complete '):
       run['preparation_only_line']=s
   run['returncode']=child.wait()
  run['end_counters']=counters(pgid,a.cpu); run['peak_process_group_rss_bytes']=max((x['process_group_rss_bytes'] for x in run['samples']),default=0); run['peak_cgroup_nonreclaim_bytes']=max((x['cgroup_nonreclaim_bytes'] for x in run['samples']),default=0); run['wall_seconds']=(time.monotonic_ns()-start)/1e9; rusage_after=resource.getrusage(resource.RUSAGE_CHILDREN)
  # Counters are process-group snapshots; cumulative deltas are summed by pid.
  def aggregate(rows): return {k:sum(x[k] for x in rows) for k in ('utime_ticks','stime_ticks','sched_runtime_ns','sched_runqueue_ns')}
  b=aggregate(run['start_counters']['processes']); e=aggregate(run['end_counters']['processes'])
  run['process_delta']={k:(None if not run['end_counters']['processes'] else e[k]-b[k]) for k in b}; run['process_cpu_seconds']=(rusage_after.ru_utime-rusage_before.ru_utime)+(rusage_after.ru_stime-rusage_before.ru_stime)
  run['sched_runtime_seconds']=None if run['process_delta']['sched_runtime_ns'] is None else run['process_delta']['sched_runtime_ns']/1e9; run['sched_runqueue_seconds']=None if run['process_delta']['sched_runqueue_ns'] is None else run['process_delta']['sched_runqueue_ns']/1e9
  run['steal_ticks_delta']=None if run['start_counters']['selected_cpu_steal_ticks'] is None or run['end_counters']['selected_cpu_steal_ticks'] is None else run['end_counters']['selected_cpu_steal_ticks']-run['start_counters']['selected_cpu_steal_ticks']
  run['steal_seconds_delta']=None if run['steal_ticks_delta'] is None else run['steal_ticks_delta']/TICKS
  run['wall_minus_selected_cpu_steal_approx_seconds']=None if run['steal_seconds_delta'] is None else run['wall_seconds']-run['steal_seconds_delta']
  run['interval_deltas']={}
  for k in ('nr_periods','nr_throttled','throttled_usec','usage_usec','user_usec','system_usec'):
   x=run['start_counters']['cgroup_cpu_stat'].get(k); y=run['end_counters']['cgroup_cpu_stat'].get(k)
   if x is not None and y is not None: run['interval_deltas'][k]=y-x
  for phase,(lo,hi) in spans.items():
   if lo not in run['events'] or hi not in run['events']: continue
   x,y=run['snapshots'][lo],run['snapshots'][hi]
   phasecpu=lambda q:{k:sum(z[k] for z in q['processes']) for k in ('utime_ticks','stime_ticks','sched_runtime_ns','sched_runqueue_ns')}
   u,v=phasecpu(x),phasecpu(y); wall=(run['events'][hi]-run['events'][lo])/1e9
   available=bool(x['processes'] and y['processes'])
   st=None if x['selected_cpu_steal_ticks'] is None or y['selected_cpu_steal_ticks'] is None else y['selected_cpu_steal_ticks']-x['selected_cpu_steal_ticks']
   cpu_ticks=None if not available else (v['utime_ticks']-u['utime_ticks'])+(v['stime_ticks']-u['stime_ticks'])
   sched_run=None if not available else v['sched_runtime_ns']-u['sched_runtime_ns']; sched_queue=None if not available else v['sched_runqueue_ns']-u['sched_runqueue_ns']
   sched_ok=available and not (sched_run==0 and (cpu_ticks or 0)>0)
   run.setdefault('phase_metrics',{})[phase]={'wall_seconds':wall,'process_cpu_seconds':None if cpu_ticks is None else cpu_ticks/TICKS,'sched_runtime_seconds':None if not sched_ok else sched_run/1e9,'sched_runqueue_seconds':None if not sched_ok else sched_queue/1e9,'schedstat_available':sched_ok,'cpu_steal_ticks_delta':st,'cpu_steal_seconds_delta':None if st is None else st/TICKS,'wall_minus_cpu_steal_approx_seconds':None if st is None else wall-st/TICKS}
  if 'decode_start' in run['events']:
   run['initial_start_to_decode_wall_seconds']=(run['events']['decode_start']-run['start_counters']['wall_monotonic_ns'])/1e9
  if 'guest_end' in run['events'] and 'output_end' in run['events']:
   run['candidate0_to_terminal_output_wall_seconds']=(run['events']['output_end']-run['events']['guest_end'])/1e9
  run['terminal_observed']=bool(run.get('candidate0') and run.get('terminal_line') and run.get('readiness_line')=='decode: ready obligations=0' and run['returncode']==0 and re.search(r'run: (finalized_exit code=|undefined_behavior |unsupported |failed |pending )',run['terminal_line']))
  run['finalized_exit_observed'] = bool(run.get('terminal_line', '').startswith('run: finalized_exit code=') and run['returncode'] == 0)
  run['preparation_only_observed'] = bool(run.get('preparation_only_line') and 'prepare_end' in run['events'] and run.get('readiness_line') == 'decode: ready obligations=0' and run['returncode'] == 0)
  result['runs'].append(run); (OUT/f'{a.name}-{i:02d}.json').write_text(json.dumps(run,indent=2)+'\n'); print(json.dumps({'run':i,'wall_seconds':run['wall_seconds'],'process_cpu_seconds':run['process_cpu_seconds'],'steal_seconds_delta':run['steal_seconds_delta'],'terminal_observed':run['terminal_observed'],'returncode':run['returncode']}),flush=True)
 (OUT/f'{a.name}-summary.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__': main()
