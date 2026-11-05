"""Finite generic-runtime parity cases and conservative-field coverage audit."""
import json
from pathlib import Path
import re
import sys
from build_prepared_image_cases import encode

ROOT=Path(__file__).resolve().parents[2]

def between(source,start,end):
    return source[source.index(start):source.index(end,source.index(start))]

def pattern_strings(source):
    result=set()
    for line in source.splitlines():
        if line.lstrip().startswith('|') and '=>' in line:
            result.update(re.findall(r'"([^"\\]*)"',line.split('=>',1)[0]))
    return result

def cases():
    decoder=(ROOT/'Miri/Input/DecoderValues.lean').read_text()
    graph=(ROOT/'Miri/Input/JsonTraversalCache.lean').read_text()
    classified=set(re.findall(r'"([^"\\]*)"',between(graph,'private def runtimeFieldClass','private def runtimeFieldRisk')))
    category_keys=pattern_strings(between(decoder,'def typedEnumCategory?','def parseInlineTag'))
    domain_keys=pattern_strings(between(decoder,'def childDomain','def recognizedAutoDomain'))
    span_keys=set(re.findall(r'"([^"\\]*)"',between(decoder,'def isSourceSpanJson','def typeShapeKind')))
    required=category_keys|domain_keys|span_keys|{'status','kind','variant','operator','user_type_projection','span','scope'}
    if required-classified:raise ValueError('runtime summary classifier misses decoder fields: '+repr(sorted(required-classified)))
    values=['synthetic_unknown',{}, {'kind':'synthetic_unknown'},
        {'kind':'synthetic_unknown','status':'supported'}, {'kind':1,'status':0}, {'status':'unsupported'}]
    for key in sorted(classified):
        for value in values:
            item={key:value}
            yield {'probe':item}
            yield {'records':[item,item]}
            yield {'hir_id':item}
            yield {'operand':{'kind':'RuntimeChecks','status':'supported',key:value}}
            yield {'statements':[{'kind':{'variant':'AscribeUserType','status':'supported',key:value}}]}
    span=dict(lo=1,hi=2,start=dict(line=1,column=2),end=dict(line=1,column=3),ctxt='root',file='test.rs')
    for item in [span,{**span,'lo':'bad'}, {**span,'start':None}, {'lo':1,'hi':2},
                 dict(span=span,scope=0),dict(span=span,scope='bad'),dict(span=None,scope=0),
                 dict(span=span),dict(scope='bad'),
                 dict(status='debug_payload',phase='synthetic_unknown',span=None,scope='bad'),
                 dict(kind='Overflow',operator={}),dict(kind='Overflow',operator='bad'),
                 dict(kind='memory',status='supported',allocation_id=1,source_alloc_id=7),
                 dict(kind='function',status='supported',generic_args=[],instance_def_id=dict(crate=2,index=3)),
                 dict(status='complete',salts=[dict(allocation_id=1,salt=0),dict(status='unsupported')])]:
        yield {'probe':item}
        yield {'records':[item,item]}
    for hir in [dict(owner_def_id='def',local_id=1),dict(owner_def_id='def',local_id='bad'),{}]:
        yield {'statements':[{'kind':dict(variant='Coverage',status='supported',coverage=dict(
            kind='point',status='supported',point_kind='expr',hir_id=hir))}]}
    yield {'cast_kind':dict(kind='PointerCoercion',status='supported',coercion=dict(
        kind='Unsize',status='supported',source=dict(kind='synthetic_unknown',status='supported')))}
    yield {'phase':dict(kind='analysis',status='supported',phase='built')}
    yield {'retag':dict(kind='yes',status='supported',performs_retag=False)}
    yield {'region':dict(kind='early_parameter',status='supported')}

if __name__=='__main__':
    output=Path(sys.argv[1]);output.mkdir(parents=True,exist_ok=True)
    count=0
    for count,document in enumerate(cases(),1):
        (output/f'{count:04}.json').write_text(json.dumps(encode(document),ensure_ascii=False,separators=(',',':')))
    print(f'runtime field coverage audited; {count} shared/context/error cases generated')
