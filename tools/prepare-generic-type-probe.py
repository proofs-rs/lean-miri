#!/usr/bin/env python3
"""Extract input-bound raw material for GenericTypeProbe, never query answers.

This is a focused comparison adapter, not an interpreter input. Type shapes,
constant trees and definition identities retain compilation-local IDs exactly.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path, help='new material projection')
    args = parser.parse_args()
    raw = args.source.read_bytes()
    document = json.loads(raw)
    projection = {
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'source_byte_length': len(raw),
        'runtime_target_data_layout': document['runtime_target_data_layout'],
        'types': [{key: value for key, value in row.items() if key != 'compiler_facts'}
                  for row in document['types']],
        'definitions': [{key: row[key] for key in ('crate', 'index')}
                        for row in document['definitions']],
        'type_constants': document['type_constants'],
    }
    with args.output.open('x') as output:
        json.dump(projection, output, separators=(',', ':'))
    print(f"material={args.output.stat().st_size} bytes; source={len(raw)} bytes; "
          f"types={len(projection['types'])}; definitions={len(projection['definitions'])}; "
          f"constants={len(projection['type_constants'])}; sha256={projection['source_sha256']}")


if __name__ == '__main__':
    main()
