import json
import sys

source = json.load(open(sys.argv[1]))
closures = []
for row in source['types']:
    shape = row.get('shape', {})
    if shape.get('kind') != 'closure':
        continue
    definition = source['definitions'][shape['def_id']]
    queries = row['compiler_facts']['boolean_queries']
    if isinstance(queries, int):
        queries = source['boolean_queries'][queries]
    closures.append({
        'crate_index': definition['crate'], 'index': definition['index'],
        **{key: queries[key] for key in ['is_unpin', 'is_unsafe_unpin', 'is_freeze']},
    })
with open(sys.argv[2], 'w') as output:
    json.dump({'closures': closures}, output)
