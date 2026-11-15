#!/usr/bin/env python3
"""Select unchanged schema12 layout rows for genuine std internal locals.
Comparison-only projection. No rows are supplied to foundation readers.
"""
import json
import sys
source = json.load(open(sys.argv[1]))
assert source['schema_version'] == 12
items = [r for r in source['instances'] if r.get('def_path') == 'std::rt::lang_start_internal'
         and r['instance_kind']['kind'] == 'item']
assert len(items) == 1
body = source['bodies'][items[0]['body']]
rows = []
for local in body['locals']:
    node = source['types'][local['type']]
    rows.append(source['layout_values'][source['layouts'][node['layout']]])
closure = source['types'][body['locals'][6]['type']]
tuple_id = closure['shape']['generic_args'][-1]['value']
tuple_row = source['types'][tuple_id]
wrappers = []
for t in source['types']:
    shape = t['shape']
    if shape.get('kind') == 'adt' and shape.get('def_path') in [
            'std::process::ExitCode', 'std::sys::process::unix::common::ExitCode']:
        wrappers.append({'definition': source['definitions'][shape['def_id']],
                         'layout': source['layout_values'][source['layouts'][t['layout']]]})
method = [r for r in source['instances'] if r.get('def_path') == 'std::process::ExitCode::to_i32']
assert len(method) == 1
queries = [q for q in source['compiler_instance_abis'] if q['instance_id'] == method[0]['instance_id']]
assert len(queries) == 1 and not queries[0]['extra_argument_types']
method_abi = source['fn_abis'][queries[0]['abi_query']]
assert len(method_abi['arguments']) == 1
argument = source['abi_arguments'][method_abi['arguments'][0]]
argument_type = source['types'][argument['type']]['shape']
assert argument_type['def_path'] == 'std::process::ExitCode'
full_method_abi = dict(method_abi)
full_method_abi['arguments'] = [source['abi_arguments'][i] for i in method_abi['arguments']]
full_method_abi['return'] = source['abi_arguments'][method_abi['return']]
return_node = source['types'][full_method_abi['return']['type']]
method_mode = {'definition': source['definitions'][argument_type['def_id']], 'mode': argument['mode']}
json.dump({'rustc_commit': source['producer']['rustc_commit'], 'local_layouts': rows,
           'scalar_wrappers': wrappers, 'exitcode_method_mode': method_mode, 'exitcode_method_abi': full_method_abi,
           'method_definition': source['definitions'][method[0]['def_id']],
           'method_return_shape': return_node['shape'],
           'method_return_layout': source['layout_values'][source['layouts'][return_node['layout']]], 'capture_tuple_layout': source['layout_values'][source['layouts'][tuple_row['layout']]]},
          open(sys.argv[2], 'w'))
