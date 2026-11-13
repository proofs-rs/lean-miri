#!/usr/bin/env python3
"""Pinned finite Virtual ABI comparisons. Build the primary library before running.

The explicit oracle exporter must be the separately sealed FullLayout shadow:
source ABI admission off, local oracle bodies materialized, actual rustc receiver
FullLayout observed. This script never builds or changes the primary Lean tree.
"""
from pathlib import Path
import argparse,copy,hashlib,json,os,subprocess

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def seal(binary,manifest):
 value=json.loads(manifest.read_text())
 assert value.get('build_exit')==0 and value.get('before') and value['before']==value.get('after'),'invalid exporter source seal'
 assert sha(binary)==value['binary_sha256'],'exporter binary differs from seal'
 return value

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 for name in ['exporter','manifest','oracle-exporter','oracle-manifest','output']:
  parser.add_argument('--'+name,type=Path,required=True)
 parser.add_argument('--project-root',type=Path,default=Path(__file__).resolve().parents[1])
 parser.add_argument('--source-root',type=Path,help='Optional staged test/fixture tree for review before applying a test-only patch')
 parser.add_argument('--rustc',type=Path);parser.add_argument('--sysroot',type=Path);parser.add_argument('--lake',default='lake')
 args=parser.parse_args();root=args.project_root.resolve();sources=(args.source_root or root).resolve();out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
 candidate=seal(args.exporter,args.manifest);oracle=seal(args.oracle_exporter,args.oracle_manifest)
 assert any('FullLayout' in str(x) for x in oracle.get('adapters',[])),'oracle seal must identify actual receiver FullLayout adapter'
 env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_MIRI_TRACE_ABI_CALLS='1',LEAN_MIRI_LAYOUT_QUERY_TRACE='1')
 rustup=Path(env.get('RUSTUP_HOME',root/'.rustup'));toolchain=rustup/'toolchains/miri-exporter-8144389c895d'
 rustc=(args.rustc or toolchain/'bin/rustc').resolve();sysroot=(args.sysroot or Path(env.get('MIRI_SYSROOT',root/'scratch/miri-sysroot'))).resolve()
 env['PATH']=str(rustc.parent)+':'+env['PATH'];env['LD_LIBRARY_PATH']=str(rustc.parent.parent/'lib')+(':'+env['LD_LIBRARY_PATH'] if env.get('LD_LIBRARY_PATH') else '');env['MIRI_SYSROOT']=str(sysroot);env['TMPDIR']=str(out/'temp');(out/'temp').mkdir()
 compiler=subprocess.check_output([str(rustc),'-vV'],env=env,text=True);assert 'commit-hash: 8144389c895da997dbdecaa635e41d6a50be6ffd' in compiler,'unpinned rustc'
 exports=[];checks=[];counts={};used_sources=set()
 def source(relative):
  staged=sources/relative
  return staged if staged.exists() else root/relative
 def run(command,log,expected=None):
  assert not log.exists(),'refuse to overwrite evidence'
  with log.open('w') as handle:result=subprocess.run(list(map(str,command)),cwd=root,env=env,stdout=handle,stderr=subprocess.STDOUT)
  valid=result.returncode==0 if expected is None else result.returncode!=0 and expected in log.read_text()
  checks.append({'command':list(map(str,command)),'exit':result.returncode,'expected_rejection':expected,'verified':valid,'log':str(log)})
  (out/'checks.json').write_text(json.dumps(checks,indent=2)+'\n');assert valid,f'failed check preserved: {log}'
 def export(key,fixture,entry,role,opt,panic,expected=None,flags=()):
  used_sources.add(fixture)
  binary=args.exporter if role=='candidate' else args.oracle_exporter;path=out/(key+'-'+role+'.json');log=out/(key+'-'+role+'.export.log')
  run([binary,'--output',path,'--root',entry,'--',fixture,'--edition=2024','--crate-type=lib','--crate-name=virtual_abi_checks',f'-Copt-level={opt}',f'-Cpanic={panic}','-Zmir-opt-level=0',*flags],log)
  doc=json.loads(path.read_text());virtual=[x for x in doc['instances'] if x['instance_kind']['kind']=='virtual']
  if role=='candidate' and expected is not None:
   assert len(virtual)==expected and all(x['kind']=='identity_only' and 'virtual_identity' not in x for x in virtual),'source domain retains eager virtual answers'
   ids={x['instance_id'] for x in virtual};assert not any(x['instance_id'] in ids for x in doc['compiler_instance_abis'])
   trace=[x for x in log.read_text().splitlines() if x.startswith('lean_miri_instance_abi_call') and 'Virtual(' in x]
   assert trace and all('queried=false' in x for x in trace) and any('route=identity-source' in x for x in trace),'hidden Virtual FnAbi query'
  if role=='oracle':
   for row in doc['compiler_instance_abis']:
    node=doc['instances'][row['instance_id']]
    if node['instance_kind']['kind']!='virtual' or doc['definitions'][node['def_id']]['crate']!=0:continue
    abi=doc['fn_abis'][row['abi_query']];argument=doc['abi_arguments'][abi['arguments'][0]];physical=doc['layout_values'][doc['layouts'][argument['layout']]]
    assert 'size_bytes' in physical and 'primitive_recipe' not in physical,'oracle receiver is not actual FullLayout'
  exports.append({'key':key,'role':role,'path':str(path),'sha256':sha(path),'source_sha256':sha(fixture),'binary_sha256':sha(binary),'invocation':doc['invocation']});(out/'exports.json').write_text(json.dumps(exports,indent=2)+'\n')
  return path
 def lean(key,test,paths,expected=None):
  file=source(Path('tests/compiler_queries')/test);used_sources.add(file);run([args.lake,'env','lean','--run',file,*paths],out/(key+'.lean.log'),expected)
 def full_count(key):
  doc=json.loads((out/(key+'-oracle.json')).read_text());rows=[]
  for query in doc['compiler_instance_abis']:
   node=doc['instances'][query['instance_id']]
   if node['instance_kind']['kind']=='virtual' and doc['definitions'][node['def_id']]['crate']==0:rows.append({'definition':node['instance_kind'],'arguments':node['generic_args'],'abi':query['abi_query']})
  assert len({json.dumps(x,sort_keys=True) for x in rows})==len(rows),'duplicate oracle comparison key';counts[key]=rows
 fixtures={'baseline':('source-virtual-instance-abi.rs','root','WorldVirtualInstanceAbi.lean',8),'byvalue':('source-virtual-by-value-abi.rs','source_call','WorldVirtualReceiverAbi.lean',1),'transparent1':('source-virtual-transparent-abi.rs','source_call','WorldVirtualReceiverAbi.lean',1),'transparent2':('source-virtual-transparent-two-abi.rs','source_call','WorldVirtualReceiverAbi.lean',1),'tracked':('source-virtual-tracked-abi.rs','source_call','WorldTrackedVirtualAbi.lean',1)}
 for family,(fixture,entry,test,expected) in fixtures.items():
  for opt in [0,3]:
   for panic in ['abort','unwind']:
    key=f'{family}-opt{opt}-{panic}';paths=[export(key,source(Path('tests/repro/compiler-queries')/fixture),entry,role,opt,panic,expected) for role in ['candidate','oracle']];lean(key,test,paths);full_count(key)
 for role,entry in [('candidate','base'),('oracle','oracle')]:export('novel',source(Path('tests/repro/compiler-queries/source-novel-virtual-abi.rs')),entry,role,3,'abort',1)
 lean('novel','NovelVirtualInstanceAbi.lean',[out/'novel-candidate.json',out/'novel-oracle.json']);full_count('novel')
 for role in ['candidate','oracle']:export('positive-auto',source(Path('tests/repro/compiler-queries/source-virtual-auto-abi.rs')),'root',role,3,'unwind',2,('-Zllvm-writable=true',))
 lean('positive-auto','WorldVirtualAutoAbi.lean',[out/'positive-auto-candidate.json',out/'positive-auto-oracle.json']);full_count('positive-auto')
 for role in ['candidate','oracle']:export('three-wrapper',source(Path('tests/repro/compiler-queries/source-virtual-transparent-three-abi.rs')),'source_call',role,0,'abort')
 lean('three-wrapper','VirtualReceiverCap.lean',[out/'three-wrapper-candidate.json',out/'three-wrapper-oracle.json'])
 export('field-boundaries',source(Path('tests/repro/compiler-queries/source-virtual-field-boundaries.rs')),'boundary','candidate',0,'abort')
 # Black-box rustc oracles are compiled separately, with no candidate gate code.
 field_binary=out/'field-oracle';receiver_binary=out/'receiver-oracle'
 for tool,binary in [('virtual-receiver-field-oracle.rs',field_binary),('virtual-receiver-abi-oracle.rs',receiver_binary)]:
  file=source(Path('tools')/tool);used_sources.add(file);run([rustc,'--edition=2024',file,'-o',binary],out/(tool+'.build.log'))
 doc=json.loads((out/'field-boundaries-candidate.json').read_text());run([field_binary,*doc['invocation']['rustc_args']],out/'field-oracle.json')
 lean('field-boundaries','WorldVirtualReceiverFields.lean',[out/'field-boundaries-candidate.json',out/'field-oracle.json'])
 for family in ['byvalue','transparent1','transparent2','tracked']:
  for opt in [0,3]:
   for panic in ['abort','unwind']:
    key=f'{family}-opt{opt}-{panic}';doc=json.loads((out/(key+'-candidate.json')).read_text());run([receiver_binary,*doc['invocation']['rustc_args']],out/(key+'.independent-rust-oracle.log'))
 # Mutate actual results; never construct fake expected MIR or source bodies.
 mutations=[('byvalue','wrong-original',None),('transparent1','wrong-original-wrapper',None),('tracked','wrong-fixed-count',None),('tracked','wrong-static-location',None),('byvalue','wrong-self-nonnull',16),('transparent1','wrong-wrapper-nonnull',16),('tracked','wrong-caller-noalias',8)]
 for family,label,bits in mutations:
  key=family+'-opt0-abort';doc=json.loads((out/(key+'-oracle.json')).read_text());node=next(x for x in doc['instances'] if x['instance_kind']['kind']=='virtual');abi=doc['fn_abis'][node['virtual_identity']['fn_abi']]
  if bits:doc['abi_arguments'][abi['arguments'][-1 if family=='tracked' else 0]]['mode']['attributes']['regular_bits']|=bits
  elif label=='wrong-fixed-count':abi['fixed_count']+=1
  elif label=='wrong-static-location':doc['abi_arguments'][abi['arguments'][-1]]['type']=doc['compiler_runtime_primitives']['caller_location_type']
  else:doc['abi_arguments'][abi['arguments'][0]]['type']=doc['types'][node['virtual_identity']['function_type']]['shape']['signature']['inputs'][0]
  wrong=out/(label+'-oracle.json');wrong.write_text(json.dumps(doc)+'\n');lean(label,'WorldTrackedVirtualAbi.lean' if family=='tracked' else 'WorldVirtualReceiverAbi.lean',[out/(key+'-candidate.json'),wrong],'complete source Virtual ABI differs from pinned rustc')
 original=json.loads((out/'tracked-opt0-abort-candidate.json').read_text());definition=next(i for i,n in enumerate(original['definitions']) if (n.get('adt_declaration') or {}).get('lang_item')=='panic_location')
 for label,test in [('forged-recipe','VirtualCallerRecipeReject.lean'),('missing-lang-item','VirtualCallerLangItemReject.lean'),('missing-raw-field','VirtualCallerRawFieldReject.lean')]:
  doc=copy.deepcopy(original)
  if label=='forged-recipe':ref=doc['compiler_runtime_primitives']['caller_location_type'];child=doc['types'][ref]['shape']['pointee'];doc['layout_values'][doc['layouts'][doc['types'][child]['layout']]]={'primitive_recipe':'u32'}
  elif label=='missing-lang-item':doc['definitions'][definition]['adt_declaration']['lang_item']=None
  else:doc['definitions'][definition]['generic_template']['fields'].pop()
  wrong=out/(label+'-source.json');wrong.write_text(json.dumps(doc)+'\n');paths=[out/'tracked-opt0-abort-candidate.json',wrong] if label=='missing-raw-field' else [wrong,out/'tracked-opt0-abort-oracle.json'];lean(label,test,paths)
 run(['python3',root/'tools/check-virtual-source-decode.py',out/'baseline-opt0-abort-candidate.json','--output',out/'decoder-controls','--lake',args.lake],out/'decoder-controls.log')
 count=sum(map(len,counts.values()));assert count==51,count
 report={'whole_FnAbi_unique_method_policy_count':count,'comparisons':counts,'atSite_and_negative_replays_counted_again':False,'source_cache_controls':'All normalized-answer catalogs removed, instance/body stores empty, projection/boolean/ADTfacts removed, cached closedADTfieldTypeIds poisoned; complete raw definition field templates retained.','source_files_sha256':{str(x):sha(x) for x in sorted(used_sources)},'exporter_seals':{'default':str(args.manifest),'oracle':str(args.oracle_manifest)},'limits':'Finite pinned x86_64/AS0 comparison; neither universal ABI correctness nor whole-guest UB freedom.'};(out/'result.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS',count,'complete unique source Virtual FnAbi comparisons plus strict controls')
if __name__=='__main__':main()
