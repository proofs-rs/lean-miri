#!/usr/bin/env python3
"""Inspect an exported body's canonical index using lowerCoreProgram's order.

This is a source-derived diagnostic adapter, not a decoder or safety check.
Use the same bytes that passed strict readiness. Root/promoted bodies precede
instance/promoted bodies; missing promoted bodies do not consume an index.
"""
import argparse
import json
import pathlib


def canonical_bodies(document):
    nodes = document.get('shared_payloads', {}).get('nodes', [])

    def deref(value):
        seen = set()
        while isinstance(value, dict) and '$lean_miri_shared_ref' in value:
            index = value['$lean_miri_shared_ref']
            if index in seen:
                raise ValueError('cyclic shared reference')
            seen.add(index)
            if not isinstance(index, int) or index < 0 or index >= len(nodes):
                raise ValueError('shared reference outside catalog')
            value = nodes[index]
        return value

    def field(value, name, default=None):
        return deref(deref(value).get(name, default))

    result = []

    def append(body, path, name):
        result.append({'source_path': path, 'definition_path': field(body, 'def_path', name),
                       'body': deref(body)})

    def promoted(owner, path, name):
        for i, child in enumerate(field(owner, 'promoted_bodies', [])):
            body = field(child, 'body')
            if body is not None:
                append(body, f'{path}.promoted_bodies[{i}].body', f'{name}::promoted[{i}]')

    for i, body in enumerate(deref(document['bodies'])):
        path = f'bodies[{i}]'
        name = field(body, 'def_path', path)
        append(body, path, name)
        promoted(body, path, name)
    for i, instance in enumerate(deref(document['instances'])):
        body = field(instance, 'body')
        if body is None:
            continue
        path = f'instances[{i}]'
        name = field(instance, 'def_path', path)
        append(body, path + '.body', name)
        if field(body, 'promoted_bodies', []):
            promoted(body, path + '.body', name)
        else:
            promoted(instance, path, name)
    return result, deref


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=pathlib.Path)
    parser.add_argument('--body', type=int, required=True)
    parser.add_argument('--block', type=int, default=0)
    parser.add_argument('--statement', type=int, default=0)
    args = parser.parse_args()
    bodies, deref = canonical_bodies(json.loads(args.input.read_text()))
    if args.body < 0 or args.body >= len(bodies):
        parser.error('body index out of range')
    selected = bodies[args.body]

    def expand(value):
        value = deref(value)
        if isinstance(value, dict):
            return {k: expand(v) for k, v in value.items()}
        if isinstance(value, list):
            return [expand(v) for v in value]
        return value

    body = selected['body']
    blocks = deref(body['basic_blocks'])
    if args.block < 0 or args.block >= len(blocks):
        parser.error('block index out of range')
    block = deref(blocks[args.block])
    statements = deref(block['statements'])
    if args.statement < 0 or args.statement > len(statements):
        parser.error('statement index out of range')
    at_terminator = args.statement == len(statements)
    node = block['terminator'] if at_terminator else statements[args.statement]
    print(json.dumps({'body_index': args.body, 'source_path': selected['source_path'],
        'definition_path': selected['definition_path'], 'block': args.block,
        'statement_index': args.statement, 'at_terminator': at_terminator,
        'node': expand(node)}, indent=2))


if __name__ == '__main__':
    main()
