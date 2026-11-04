#!/usr/bin/env python3
"""Encode retained schema-3 decoder cases as typed graph rows for parity tests.

This independent test adapter preserves read-only container aliases from the
strict Python reader. It does not implement compiler queries or MIR semantics.
"""
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from mir_json import load_mir_document


def encode(document):
    fields, field_ids, rows, containers, scalars = [], {}, [], {}, {}

    def visit(value):
        container = isinstance(value, (list, dict))
        key = id(value) if container else json.dumps(value, ensure_ascii=False, separators=(',', ':'))
        memo = containers if container else scalars
        if key in memo:
            return memo[key]
        if value is None:
            row = [0]
        elif type(value) is bool:
            row = [2 if value else 1]
        elif type(value) in (int, float):
            row = [3, value]
        elif isinstance(value, str):
            row = [4, value]
        elif isinstance(value, list):
            row = [5, [visit(item) for item in value]]
        else:
            pairs = []
            for name, item in sorted(value.items()):
                if name not in field_ids:
                    field_ids[name] = len(fields)
                    fields.append(name)
                pairs.append([field_ids[name], visit(item)])
            row = [6, pairs]
        index = len(rows)
        rows.append(row)
        memo[key] = index
        return index

    root = visit(document)
    return dict(schema='lean-miri-prepared-image', schema_version=1,
                fields=fields, nodes=rows, root=root)


if __name__ == '__main__':
    source, output = map(Path, sys.argv[1:])
    output.mkdir(parents=True, exist_ok=True)
    for path in sorted(source.glob('*.json')):
        # Source ID errors are business-data errors, and must stay so in either transport.
        document = load_mir_document(path)
        (output / path.name).write_text(json.dumps(encode(document), ensure_ascii=False,
                                                   separators=(',', ':')) + '\n')
