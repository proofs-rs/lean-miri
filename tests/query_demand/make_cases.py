#!/usr/bin/env python3
"""Mutate fresh exporter evidence; never fabricate compiler layouts/identities."""
import argparse
import copy
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document, encode_mir_document

p = argparse.ArgumentParser()
p.add_argument('base', type=Path)
p.add_argument('output', type=Path)
p.add_argument('--tls-base', type=Path)
a = p.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
# The loader intentionally preserves graph aliases. Query mutations model
# independent inline JSON values, so expand to an ordinary mutable tree once
# before copying and editing individual cases.
base = json.loads(json.dumps(load_mir_document(a.base)))
# Mutations edit the diagnostic view; save rebuilds numeric semantic tables.
cases = []

def save(name, value):
    (a.output / name).write_text(json.dumps(encode_mir_document(value), indent=2) + '\n')

save('plain.json', base)

def add(name, value, ready, provider='none', index=0, baseline='plain.json', **extra):
    save(name + '.json', value)
    cases.append(dict(file=name + '.json', baseline=baseline, ready=ready,
                      provider=provider, index=index, **extra))

def diagnostic(doc, path):
    doc.setdefault('selected_scope', {}).setdefault('retained_catalog_obligations', []).append(
        dict(path=path, type_id=10**30, reason='qa23 invalid retained compiler evidence'))

def unsupported():
    return dict(type_id=10**30, reason='qa23 invalid compiler evidence')

for family, catalog, suffix, provider in [
    ('native', 'compiler_native_signature_queries', '.signature_query', 'native'),
]:
    rows = base[catalog]
    index = next((i for i, row in enumerate(rows)
                  if (row['signature_query'] if suffix else row).get('kind') != 'unsupported'), None)
    if index is None:
        raise ValueError(f'fresh compiler export has no supported {catalog} row')
    doc = copy.deepcopy(base)
    if suffix:
        doc[catalog][index]['signature_query'] = unsupported()
    else:
        doc[catalog][index].update(unsupported())
    add(family + '-demand', doc, True, provider, index)
    retained = copy.deepcopy(doc)
    diagnostic(retained, f'{catalog}[{index}]{suffix}')
    add(family + '-retained', retained, False, index=index)
    for label, path in [
        ('leading-zero', f'{catalog}[00]{suffix}'),
        ('leading-one', f'{catalog}[01]{suffix}'),
        ('empty', f'{catalog}[]{suffix}'),
        ('signed', f'{catalog}[-1]{suffix}'),
        ('extra-bracket', f'{catalog}[0][1]{suffix}'),
        ('nondigit', f'{catalog}[x]{suffix}'),
        ('unknown-descendant', f'{catalog}[0]{suffix}.unknown'),
        ('similar-prefix', f'{catalog}_shadow[0]{suffix}'),
    ]:
        negative = copy.deepcopy(base)
        diagnostic(negative, path)
        add(f'{family}-{label}', negative, False)
    nested = copy.deepcopy(base)
    target = nested[catalog][index]['signature_query'] if suffix else nested[catalog][index]
    target['qa23_unknown_descendant'] = dict(kind='Cast', vtable_allocation=dict(kind='dynamic_vtable_upcast'))
    add(family + '-actual-unknown-descendant', nested, False, index=index)

if a.tls_base:
    tls = json.loads(json.dumps(load_mir_document(a.tls_base)))
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
    nodes = list(collect(tls['bodies']))
    if not nodes or not any('initializer' in n for n in nodes):
        raise ValueError('TLS baseline lacks actual supported inline ThreadLocalRef initializer')
    definition = next(n['def_id'] for n in nodes if 'initializer' in n)
    doc = copy.deepcopy(tls)
    for node in collect(doc['bodies']):
        if node['def_id'] == definition:
            node['initializer'] = unsupported()
    # Required inline TLS allocation images are validated by both decoders.
    add('tls-initializer-demand', doc, False, baseline='tls-plain.json', definition=definition)
    nested = copy.deepcopy(tls)
    next(n for n in collect(nested['bodies']) if n['def_id'] == definition)['initializer']['qa23_unknown_descendant'] = dict(kind='Cast', vtable_allocation=dict(kind='dynamic_vtable_upcast'))
    add('tls-unknown-descendant', nested, False, baseline='tls-plain.json')
    lookalike = copy.deepcopy(tls)
    lookalike['qa23_initializer_lookalike'] = dict(kind='ThreadLocalRef', def_id=dict(crate=0, index=0), initializer=dict(allocation=dict(allocation_id=10**30)))
    add('tls-outside-body-lookalike', lookalike, False, baseline='tls-plain.json')

save('cases.json', dict(cases=cases, source_exports=dict(
    base=str(a.base), tls_base=str(a.tls_base) if a.tls_base else None)))
print(f'wrote {len(cases)} fresh-export mutations to {a.output}')
