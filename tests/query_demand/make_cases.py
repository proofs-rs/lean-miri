#!/usr/bin/env python3
"""Mutate fresh typed compiler evidence without inventing layouts or identities."""
import argparse
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document

p = argparse.ArgumentParser()
p.add_argument('base', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--tls-base', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
base = load_mir_document(a.base)
cases = []


def save(name, value):
    (a.output / name).write_text(json.dumps(value, indent=2) + '\n')


def add(name, value, ready, provider='none', index=0, baseline='plain.json', **extra):
    save(name + '.json', value)
    cases.append(dict(file=name + '.json', baseline=baseline, ready=ready,
                      provider=provider, index=index, **extra))


save('plain.json', base)
rows = base['compiler_native_signature_queries']
if not rows:
    raise ValueError('fresh compiler export has no native signature query')
index = 0
add('native-control', base, True, 'native', index)
for name, mutate in [
    ('signature-shape', lambda row: row.update(signature_query={})),
    ('input-type', lambda row: row['signature_query'].update(inputs=[len(base['types'])])),
    ('output-type', lambda row: row['signature_query'].update(output=len(base['types']))),
    ('instance', lambda row: row.update(instance_id=len(base['instances']))),
]:
    doc = copy.deepcopy(base)
    mutate(doc['compiler_native_signature_queries'][index])
    add('native-' + name, doc, False, index=index)

extra = copy.deepcopy(base)
extra['compiler_native_signature_queries'][index]['ignored_extension'] = {
    'kind': 'Cast', 'type_id': 10**30, 'allocation': 10**30,
}
add('native-irrelevant-extension', extra, True)

if a.tls_base:
    tls = load_mir_document(a.tls_base)
    save('tls-plain.json', tls)

    def collect(value):
        if isinstance(value, dict):
            if value.get('kind') == 'ThreadLocalRef':
                yield value
            for child in value.values():
                yield from collect(child)
        elif isinstance(value, list):
            for child in value:
                yield from collect(child)

    nodes = list(collect(tls['statement_kinds']))
    if not nodes or not any('initializer' in node for node in nodes):
        raise ValueError('TLS baseline lacks an inline ThreadLocalRef initializer')
    definition = next(node['def_id'] for node in nodes if 'initializer' in node)
    add('tls-control', tls, True, 'tls', baseline='tls-plain.json', definition=definition)
    doc = copy.deepcopy(tls)
    for node in collect(doc['statement_kinds']):
        if node['def_id'] == definition:
            node['initializer'] = {}
    add('tls-initializer-shape', doc, False, baseline='tls-plain.json')
    doc = copy.deepcopy(tls)
    next(node for node in collect(doc['statement_kinds']) if node['def_id'] == definition)['def_id'] = len(tls['definitions'])
    add('tls-definition-bounds', doc, False, baseline='tls-plain.json')
    extra = copy.deepcopy(tls)
    extra['ignored_extension'] = {'kind': 'ThreadLocalRef', 'def_id': 10**30,
                                  'initializer': {'allocation': 10**30}}
    add('tls-irrelevant-extension', extra, True, baseline='tls-plain.json')

save('cases.json', dict(cases=cases, source_exports=dict(
    base=str(a.base), tls_base=str(a.tls_base) if a.tls_base else None)))
print(f'wrote {len(cases)} fresh-export mutations to {a.output}')
