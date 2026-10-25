#!/usr/bin/env python3
"""Independently check fixed guided logs, typed prefixes and MIR step projections.

Usage: check_guided_pairs.py CASES_JSON RESULT_JSON
CASES_JSON is a four-row list with case, snapshot, log, prefix, result paths.
This reads evidence only; it executes neither Lean nor a guest.
"""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
from mir_json import load_mir_document
ORIGINAL_SOURCES={'fence-acqrel': ['/workspace/lean-miri/docs/verification/sc-ordering-controls264/inputs/259-fence-acqrel-yield-control.rs'], 'fence-sc': ['/workspace/lean-miri/docs/verification/sc-ordering-controls264/inputs/259-fence-sc-yield.rs'], 'rmw-relaxed': ['/workspace/lean-miri/docs/verification/sc-ordering-controls264/inputs/259-rmw-relaxed-yield-control.rs'], 'rmw-sc': ['/workspace/lean-miri/docs/verification/sc-ordering-controls264/inputs/259-rmw-sc-yield.rs']}
SOURCE_HASHES={'fence-acqrel': '2c6645e8da4e849ea7e13e3a1bcc5c1293a8965e7ab53605997a18d412048c26', 'fence-sc': 'e55a059e733243d97e9a4ef5aa7e3ff9a264dcfbdcd07b74c04fc79fffc76905', 'rmw-relaxed': '31042ff16963a0730d1d5d6f511bf240bc293d3a3e46880b8ab8ba7cea90975e', 'rmw-sc': '059cb871809b85b579e70e0ae372203681be184c82df093d2032dccd38a00be0'}
def need(ok,msg):
    if not ok:raise AssertionError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(p):return Path(p) if Path(p).is_absolute() else ROOT/p
def events(text):
    before,tail=text.split('choice_events=#[',1)
    final=int(re.findall(r'choice_cursor=(\d+)',before)[-1])
    chunks=re.split(r'\{ request :=',tail)[1:]
    out=[]
    for c in chunks:
        req=re.search(r'Request\.(index|bernoulli)\s*\(Miri\.Interpreter\.ExecutionChoices\.(IndexSite|BoolSite)\.(\w+)\)\s*(\d+)',c)
        inp=re.search(r'Input\.(index|boolean)\s*\(Miri\.Interpreter\.ExecutionChoices\.(IndexSite|BoolSite)\.(\w+)\)\s*(\d+|true|false)',c)
        need(req is not None and inp is not None,'cannot parse complete event')
        rk,_,site,support=req.groups();ik,_,isite,value=inp.groups()
        need(site==isite,'event site mismatch')
        val=int(value) if ik=='index' else value=='true'
        if ik=='index':need(rk=='index' and val<int(support),'invalid observed index')
        else:need(rk=='bernoulli' and value in ('true','false'),'invalid observed bool')
        out.append({'request':{'kind':rk,'site':site,'support':int(support)},'input':{'kind':ik,'site':site,'value':val}})
    need(len(out)==final,f'event parse count {len(out)} != final cursor {final}')
    return out
STEP=re.compile(r'sc264_core_step thread=\{ value := (\d+) \}; choice_cursor=(\d+); frame=some \(\{ kind := Miri.Interpreter.CallInstanceKind.Item (\d+), args := #\[\] \},\s*Miri.Interpreter.FrameLocation.mir \{ block := (\d+), statementIndex := (\d+)')
def source_map(document):
    # Decoder.parseBodyCore chooses def_id, falling back to source_def_id.
    # LowerMIR.lowerCoreProgram collects roots/promoted then instance bodies;
    # lowerBodies interns their source definitions before remaining instances.
    bodies=[]
    def append(b,name,promoted=None):
        bodies.append((b,name))
        for child in (b.get('promoted_bodies',[]) or promoted or []):
            if child.get('body') is not None:bodies.append((child['body'],name+'::promoted'))
    for b in document['bodies']:append(b,b.get('def_path','root'))
    for i in document['instances']:
        if i.get('body') is not None:append(i['body'],i['def_path'],i.get('promoted_bodies'))
    definitions=[]
    def identity(b):return b.get('def_id',b.get('source_def_id'))
    for b,_ in bodies:
        d=identity(b)
        if d is not None and d not in definitions:definitions.append(d)
    for i in document['instances']:
        d=i.get('def_id')
        if d is not None and d not in definitions:definitions.append(d)
    sites={}
    workers={}
    for b,name in bodies:
        if name not in ('child_a','child_b','miri_start'):continue
        dense=definitions.index(identity(b))
        if name.startswith('child_'):workers[name]=dense
        for block in b['basic_blocks']:
            kind=block['terminator']['kind']
            if kind.get('variant')!='Call':continue
            callee=kind.get('resolution',{}).get('instance_def_path')
            sites[(dense,block['block'],len(block['statements']))]=(name,callee)
    need(set(workers)=={'child_a','child_b'},'missing exact workers')
    return sites,workers
def check(row):
    raw,log,prefix,result=map(path,(row['snapshot'],row['log'],row['prefix'],row['result']))
    txt=log.read_text();run=json.loads(result.read_text());tape=json.loads(prefix.read_text())
    sidecar=Path(str(raw)+'.miri-reference.json');side=json.loads(sidecar.read_text());data=raw.read_bytes()
    need(side['reference']['outcome']=={'kind':'exit_zero'},'selected Miri reference did not naturally exit zero')
    need(side['reference']['config']['same_tcx'] is True,'reference is not same-TyCtxt')
    need(side['miri_commit']=='7fa591d7d4dd9af8154becbc8332f8096f8323b1' and side['rustc_commit']=='8144389c895da997dbdecaa635e41d6a50be6ffd','reference source pin mismatch')
    fnv=0xcbf29ce484222325
    for byte in data:fnv=((fnv^byte)*0x100000001b3)&0xffffffffffffffff
    need(side['snapshot_byte_length']==len(data) and side['snapshot_fnv1a64']==f'{fnv:016x}','Miri sidecar/snapshot identity mismatch')
    source=ROOT/'tests/connected/fixtures'/f'{row["case"]}.rs'
    need(sha(source)==SOURCE_HASHES[row['case']],'original reviewed Rust fixture changed')
    need(side['reference']['config']['args']==ORIGINAL_SOURCES[row['case']],'reference does not identify the unchanged Rust fixture')
    need(run['exit_code']==0 and run.get('guard') is None,'guided command did not pass')
    need(run.get('inputs_before')==run.get('inputs_after'),'runtime captured inputs changed')
    need('sc_ordering_control_fixture=PASS' in txt and 'outcome=exit_zero; leak_check=true; threads=3;' in txt,'missing canonical natural success')
    need(run['log_sha256']==sha(log),'result/log hash mismatch')
    ev=events(txt);inputs=tape['inputs'];targets=tape['target_events']
    need([e['input'] for e in ev[:len(inputs)]]==inputs,'actual supplied prefix differs')
    origin=path(tape['source_events']);need(sha(origin)==tape['source_events_sha256'],'prefix source events changed')
    original=json.loads(origin.read_text())
    modifications=[i for i,(a,b) in enumerate(zip(inputs,[e['input'] for e in original])) if a!=b]
    target_indices=[t['event_index'] for t in targets]
    need(len(inputs)==target_indices[-1]+1,'prefix does not end immediately after second target')
    need(set(modifications)<=set(target_indices),'non-target supplied choice changed')
    need([e['request'] for e in ev[:len(inputs)]]==[e['request'] for e in original[:len(inputs)]],'actual prefix request sequence changed')
    sites,workers=source_map(load_mir_document(raw))
    steps=[{'thread':int(m[1]),'cursor':int(m[2]),'pc':tuple(map(int,m.group(3,4,5))),'offset':m.start()} for m in STEP.finditer(txt)]
    need(steps,'missing cursor-indexed scheduled trace')
    projected=[];active={};target_context=[]
    for n,s in enumerate(steps):
        site=sites.get(s['pc'])
        if site:
            caller,callee=site
            if caller in workers:
                # Tests use block0 write/RMW, one optional fence, one yield,
                # and the first opposite-variable load before RESULT stores.
                block=s['pc'][1]
                op=None
                if block==0 and callee and (callee.endswith('::store') or callee.endswith('::fetch_add')):op='write' if callee.endswith('::store') else 'rmw'
                elif callee=='core::sync::atomic::fence':op='fence'
                elif callee=='libc::sched_yield':op='yield'
                elif callee and callee.endswith('::load'):op='load'
                if op:
                    item=(caller,op)
                    projected.append(item);active[s['thread']]=item
        after=steps[n+1]['cursor'] if n+1<len(steps) else len(ev)
        for t in targets:
            index=t['event_index']
            if s['cursor']<=index<after:
                need(active.get(s['thread'],(None,None))[1]=='load','atomic target not inside observed worker load')
                need(ev[index]['request']=={'kind':'index','site':'atomicStale','support':t['support']},'target support disagrees')
                need(ev[index]['input']=={'kind':'index','site':'atomicStale','value':t['guided_value']},'target input disagrees')
                target_context.append({'event_index':index,'thread':s['thread'],'worker':active[s['thread']][0],'core_pc':s['pc'],'support':t['support'],'value':t['guided_value']})
    need(len(target_context)==2,'target event/step correlation missing or duplicated')
    need({x['worker'] for x in target_context}=={'child_a','child_b'},'targets do not cover both workers')
    scheduling=[e for e in ev[:len(inputs)] if e['request']['site'] in ('scheduler','preemption')]
    return {'case':row['case'],'log':str(log.relative_to(ROOT)),'log_sha256':sha(log),'prefix_sha256':sha(prefix),'snapshot_sha256':sha(raw),'miri_sidecar_sha256':sha(sidecar),'miri_seed':side['reference']['config']['rng_seed'],'miri_preemption_rate':side['reference']['config']['preemption_rate'],'original_rust_source_sha256':sha(source),'preserved_actual_prefix':True,'modified_input_indices':modifications,'dense_worker_definitions':workers,'worker_operation_projection':projected,'scheduling_projection_through_targets':scheduling,'targets':target_context}
def main():
    rows=json.loads(path(sys.argv[1]).read_text());checked=[check(r) for r in rows]
    by={r['case']:r for r in checked};pairs=[]
    for a,b in (('fence-sc','fence-acqrel'),('rmw-sc','rmw-relaxed')):
        sa,sb=by[a],by[b]
        need(sa['worker_operation_projection']==sb['worker_operation_projection'],f'{a}/{b} scheduled worker operation order differs')
        need(sa['scheduling_projection_through_targets']==sb['scheduling_projection_through_targets'],f'{a}/{b} scheduling/preemption projection through target loads differs')
        need([t['worker'] for t in sa['targets']]==[t['worker'] for t in sb['targets']],'worker load ordering differs')
        need([t['support'] for t in sb['targets']]==[2,2] and [t['value'] for t in sb['targets']]==[1,1],'weak guide did not select both older candidates')
        need(any(t['support']==1 and t['value']==0 for t in sa['targets']),'SC trace lacks observed support restriction')
        pairs.append({'positive':a,'control':b,'matched_worker_operation_order':True,'weak_oldest_ranks':[1,1],'sc_supports':[t['support'] for t in sa['targets']],'scope':'finite source/choice witness; no tested mutant or all-prefix claim'})
    result={'status':'PASS','checks':checked,'pairs':pairs,'reviewer_script_sha256':sha(__file__)}
    path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','cases':len(checked),'pairs':pairs}))
if __name__=='__main__':main()
