#!/usr/bin/env python3
"""Inspect a MIR body's exported pool ID and a selected statement or terminator.

This is a diagnostic adapter, not a decoder or safety check. References in the
printed MIR remain typed IDs.
"""
import argparse
import json
import pathlib
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def canonical_bodies(document):
    names = {}
    for root in document['body_roots']:
        names.setdefault(root['body'], root['def_path'])
        for child in root.get('promoted_bodies', []):
            names.setdefault(child['body'], f"{root['def_path']}::promoted[{child['promoted_index']}]")
    for instance in document['instances']:
        if instance.get('body') is not None:
            names.setdefault(instance['body'], instance['def_path'])
        for child in instance.get('promoted_bodies', []):
            names.setdefault(child['body'], f"{instance['def_path']}::promoted[{child['promoted_index']}]")
    for body_id in names:
        pool_entry(document, 'bodies', body_id)
    return [{'source_path': f'bodies[{index}]',
             'definition_path': names.get(index), 'body': body}
            for index, body in enumerate(document['bodies'])]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=pathlib.Path)
    parser.add_argument('--body', type=int, required=True)
    parser.add_argument('--block', type=int, default=0)
    parser.add_argument('--statement', type=int, default=0)
    args = parser.parse_args()
    bodies = canonical_bodies(load_mir_document(args.input))
    if args.body < 0 or args.body >= len(bodies):
        parser.error('body index out of range')
    selected = bodies[args.body]

    body = selected['body']
    blocks = body['basic_blocks']
    if args.block < 0 or args.block >= len(blocks):
        parser.error('block index out of range')
    block = blocks[args.block]
    statements = block['statements']
    if args.statement < 0 or args.statement > len(statements):
        parser.error('statement index out of range')
    at_terminator = args.statement == len(statements)
    node = block['terminator'] if at_terminator else statements[args.statement]
    print(json.dumps({'body_index': args.body, 'source_path': selected['source_path'],
        'definition_path': selected['definition_path'], 'block': args.block,
        'statement_index': args.statement, 'at_terminator': at_terminator,
        'node': node}, indent=2))


if __name__ == '__main__':
    main()
