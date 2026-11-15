#!/usr/bin/env python3
"""Project an independently emitted schema12 std-main oracle without changing IDs.

Only source shapes, the real std start closure instances and its actual vtable
metadata are retained. This is a comparison adapter, never foundation input.
"""
import json
import sys

source = json.load(open(sys.argv[1]))
assert (source['schema'], source['schema_version']) == ('lean-miri-rustc-mir', 12)
items = [row for row in source['instances']
         if row.get('def_path') == 'std::rt::lang_start::{closure#0}'
         and row['instance_kind']['kind'] == 'item']
assert len(items) == 1
closure = items[0]['def_id']
assert source['definitions'][closure] == {'crate': 1, 'index': 188}
self_types = [row['type_id'] for row in source['types']
              if row['shape'].get('kind') == 'closure' and row['shape'].get('def_id') == closure]
queries = [row for row in source['compiler_vtable_queries'] if row['input_type'] in self_types]
assert len(queries) == 1
selected = {items[0]['instance_id']}
for entry in queries[0]['vtable_metadata']['entries']:
    if entry['kind'] == 'method':
        selected.add(entry['instance_id'])
for row in source['instances']:
    if row['instance_kind'].get('closure_def_id') == closure:
        selected.add(row['instance_id'])
projected = {
    'oracle_schema': source['schema'], 'oracle_schema_version': source['schema_version'],
    'rustc_commit': source['producer']['rustc_commit'],
    'definitions': source['definitions'],
    'types': [{'type_id': row['type_id'], 'shape': row['shape']} for row in source['types']],
    'instances': [row for row in source['instances'] if row['instance_id'] in selected],
    'compiler_vtable_queries': queries,
}
# Keep actual generated shim MIR and ABI as comparison-only material. IDs
# remain the original document IDs; no answer is fed to foundation readers.
shims = [row for row in projected['instances']
         if row['instance_kind'].get('shim_kind') in ('vtable', 'closure_once')]
projected['shim_bodies'] = [source['bodies'][row['body']] for row in shims]
statement_ids = {statement['kind'] for body in projected['shim_bodies']
                 for block in body['basic_blocks'] for statement in block['statements']}
projected['shim_statements'] = [{'id': i, 'value': source['statement_kinds'][i]}
                                for i in sorted(statement_ids)]
projected['shim_spans'] = [{'id': i, 'value': source['spans'][i]}
                          for i in sorted({body['span'] for body in projected['shim_bodies']})]
projected['shim_abis'] = []
for row in shims:
    queries = [q for q in source['compiler_instance_abis'] if q['instance_id'] == row['instance_id']]
    assert len(queries) == 1 and not queries[0]['extra_argument_types']
    abi = source['fn_abis'][queries[0]['abi_query']]
    def argument(index):
        value = dict(source['abi_arguments'][index])
        layout = source['layout_values'][source['layouts'][value['layout']]]
        value['layout_size'] = layout['size_bytes']
        value['layout_align'] = layout['abi_align_bytes']
        return value
    value = dict(abi)
    value['return'] = argument(abi['return'])
    value['arguments'] = [argument(i) for i in abi['arguments']]
    projected['shim_abis'].append({'instance_id': row['instance_id'], 'value': value})
with open(sys.argv[2], 'w') as output:
    json.dump(projected, output, separators=(',', ':'))
