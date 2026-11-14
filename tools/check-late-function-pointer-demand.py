#!/usr/bin/env python3
"""Check fresh actual-MIR FnPtr demand capture, including an old type prefix."""
import json, pathlib, sys
source = json.loads(pathlib.Path(sys.argv[1]).read_text())
rows = [row for row in source['compiler_cast_queries'] if row['query_kind'] == 'resolve_fn_ptr' and source['definitions'][source['types'][row['input_type']]['shape']['def_id']]['crate'] == 0]
assert len(rows) == 1, f'expected one actual leaf cast, got {len(rows)}'
row = rows[0]
assert row['resolution_kind'] == 'instance', row
instance = source['instances'][row['instance_id']]
# Physical identity joins only; display names are checked after the join.
input_type = source['types'][row['input_type']]
assert input_type['shape']['kind'] == 'function_definition', input_type
assert instance['instance_kind']['kind'] == 'item', instance
assert input_type['shape']['def_id'] == instance['instance_kind']['def_id'], (input_type, instance)
print('PASS late actual FnPtr request has one complete resolution; nondemanded local FnDef headers have no rows')
