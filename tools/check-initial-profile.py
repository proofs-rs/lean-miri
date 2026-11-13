#!/usr/bin/env python3
"""Check six actual initial-profile export/cache/cold-boundary controls."""
from pathlib import Path
import argparse,os,json,subprocess,hashlib,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'ctfe-custom-rustc'))
from exporter_artifacts import verified_config,verify_config,sha
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,required=True);p.add_argument('--attempt',type=int,required=True)
p.add_argument('--exporter',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
p.add_argument('--fixture',type=Path,default=Path(__file__).resolve().parents[1]/'tests/repro/compiler-queries/initial-profile-cached.rs')
a=p.parse_args();config=verified_config(a.root,a.attempt)
executable=a.exporter.resolve();manifest=json.loads(a.manifest.read_text());digest=sha(executable)
assert manifest['binary_sha256']==digest,'Exporter differs from build manifest'
assert manifest.get('build_exit',manifest.get('exit'))==0
assert manifest.get('source_same') is True or (manifest.get('before') and manifest['before']==manifest.get('after')),'Missing unchanged-source build evidence'
run=a.out.resolve();assert not run.exists(),'Refusing existing evidence';run.mkdir(parents=True)
env=os.environ.copy();env.update(config['environment']);env['PATH']=str(Path(config['rustc']).parent)+os.pathsep+env.get('PATH','');env['LEAN_MIRI_TRACE_CONST_EVAL']='1';env['LEAN_MIRI_OBSERVE_CTFE_ROOT']='1'
fixture=a.fixture.resolve();source_sha=sha(fixture)
command=[str(executable),'--output','OUTPUT','--root','root','--',str(fixture),'--crate-name','initial_snapshot_ordinary','--crate-type=lib','--edition=2024','-Zmir-opt-level=0','-Zthreads=1','--sysroot',config['target_sysroot']]
(run/'inputs.json').write_text(json.dumps({'exporter':str(executable),'exporter_sha256':digest,'manifest':str(a.manifest.resolve()),'manifest_sha256':sha(a.manifest),'probe_manifest':config['probe_manifest'],'probe_manifest_sha256':config['probe_manifest_sha256'],'fixture':str(fixture),'fixture_sha256':source_sha},indent=2)+'\n')
cases=[('profile-cached',{'LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT':'1','LEAN_MIRI_INITIAL_QUERY_CACHE_ROOT':'Anchor::VALUE'},True,None),('auto-selected',{'LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT':'1'},True,None),('profile-disabled',{},True,None),('unknown-root',{'LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT':'1','LEAN_MIRI_INITIAL_QUERY_CACHE_ROOT':'Missing::VALUE'},False,'selected initial query-cache source is absent or ambiguous'),('mixed-profile',{'LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT':'1','LEAN_MIRI_PREPARED_ALLOC_ID_WORLD':'1'},False,'initial and prepared allocator profiles are mutually exclusive'),('disabled-with-key',{'LEAN_MIRI_INITIAL_QUERY_CACHE_ROOT':'Anchor::VALUE'},False,'selected query-cache roots require the complete initial profile')]
summary={}
for name,settings,success,message in cases:
 e=env.copy()
 for key in ['LEAN_MIRI_INITIAL_GLOBAL_SNAPSHOT','LEAN_MIRI_INITIAL_QUERY_CACHE_ROOT','LEAN_MIRI_INITIAL_QUERY_CACHE_ROOTS_JSON','LEAN_MIRI_PREPARED_ALLOC_ID_WORLD','LEAN_MIRI_INITIAL_CTFE_ROOT']:e.pop(key,None)
 e.update(settings);c=command.copy();output=run/(name+'.json');c[2]=str(output)
 (run/(name+'-command.json')).write_text(json.dumps({'argv':c,'profile_environment':settings},indent=2)+'\n')
 p=subprocess.run(c,env=e,capture_output=True,text=True);(run/(name+'.stdout')).write_text(p.stdout);(run/(name+'.stderr')).write_text(p.stderr)
 row={'exit':p.returncode,'binary_sha256':sha(executable),'source_same':sha(fixture)==source_sha};summary[name]=row
 if success:
  assert p.returncode==0,p.stderr
  doc=json.loads(output.read_text());row['json_sha256']=sha(output)
  if name=='profile-disabled':
   assert 'compiler_initial_global_snapshot' not in doc and 'compiler_initial_selected_query_cache' not in doc
  else:
   snapshot=doc['compiler_initial_global_snapshot'];tables=doc['compiler_initial_selected_query_cache'];assert len(tables)==1
   assert snapshot['phase']=='before_export_queries' and len(snapshot['globals'])==snapshot['global_count'] and len(snapshot['dedup'])==snapshot['dedup_count']
   slots=tables[0]['slots'];assert sum(s['present'] for s in slots)==2
   value=next(s['result']['value'] for s in slots if s['present'] and s['key']['family']=='value');assert value['bits_unsigned']=='17' and value['size_bytes']==4
   def nodes(v):
    if isinstance(v,dict):
     if v.get('kind') in ['unevaluated','unevaluated_const']:yield v
     for x in v.values():yield from nodes(x)
    elif isinstance(v,list):
     for x in v:yield from nodes(x)
   raw=list(nodes(doc));assert len(raw)>=2
   frozen=p.stderr.split('LEAN_MIRI_INITIAL_PROFILE_FROZEN\t',1)[1]
   assert not any(line.startswith('ctfe_root_pc\tAnchor::VALUE\t') for line in frozen.splitlines()),'selected root evaluated after initial capture'
   observations=[json.loads(line.split('\t',1)[1]) for line in p.stderr.splitlines() if line.startswith('LEAN_MIRI_INITIAL_PROFILE_LATE_OBSERVATIONS\t')];assert len(observations)==1
   row.update(global_count=snapshot['global_count'],dedup_count=snapshot['dedup_count'],raw_operand_nodes=len(raw),selected_pc_after_freeze=0,late_observations=observations[0])
 else:
  assert p.returncode==2 and message in p.stderr,(p.returncode,p.stderr)
  assert not output.exists(),'rejected profile emitted successful output'
 assert row['binary_sha256']==digest and row['source_same']
 (run/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(name,p.returncode,flush=True)
verify_config(config)
print('PASS six actual initial-profile export/cache/cold-boundary controls',run,flush=True)
