#!/usr/bin/env python3
"""Build strict codec controls from captured raw source rows, never scalar answers."""
from pathlib import Path
import json, copy, sys
rows=json.loads(Path(sys.argv[1]).read_text())
cases=[]
for i,row in enumerate(rows):cases.append({'name':f'actual-frame-{i}','accepted':True,'source':row})
def bad(name,index,mutate):
 row=copy.deepcopy(rows[index]);mutate(row);cases.append({'name':name,'accepted':False,'source':row})
bad('missing-owner-kind',2,lambda r:r.pop('owner_kind'))
bad('missing-preamble-span',2,lambda r:r.pop('preamble_def_span'))
bad('missing-def-path',2,lambda r:r.pop('def_path'))
bad('runtime-role',2,lambda r:r.update(source_role='runtime'))
bad('wrong-environment-owner',2,lambda r:r['environment_recipe'].update(owner={'crate':2,'index':69102}))
bad('wrong-policy',2,lambda r:r.update(policy='scalar_u32'))
bad('local-u32',2,lambda r:r['locals'][0]['type'].update(bits=32))
bad('no-return-local',2,lambda r:r.update(locals=[]))
bad('unary-neg',2,lambda r:r['blocks'][0]['statements'][0]['kind']['value'].update(op='neg'))
bad('literal-u32',2,lambda r:r['blocks'][0]['statements'][0]['kind']['value']['operand']['value'].update(bits=32))
bad('literal-overflow',2,lambda r:r['blocks'][0]['statements'][0]['kind']['value']['operand']['value'].update(value=str(2**64)))
bad('reference-declared-u32',0,lambda r:r['required_consts'][0]['declared_type'].update(bits=32))
bad('promoted-root',2,lambda r:r.update(promoted=0))
bad('generic-frame',2,lambda r:r.update(parameters=['type']))
bad('obsolete-answer-field',2,lambda r:r.update(normalized_answer=18446744073709551615))
bad('absent-source-scope',2,lambda r:r['blocks'][0]['statements'][0]['source'].update(scope=len(r['source_scopes'])))
bad('aggregate-generic-arg',0,lambda r:r['required_consts'][0].update(arguments=[{'kind':'atom','sort':'aggregate','tag':'pattern_not_null','payload':''}]))
Path(sys.argv[2]).write_text(json.dumps(cases,indent=2));print('rows',len(rows),'negative',len(cases)-len(rows))
