#!/usr/bin/env python3
"""Synthetic compiler-payload and retained-diagnostic parity cases, never Rust runs."""
import copy
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools'))
from mir_json import load_mir_document
from build_prepared_image_cases import encode


def main():
    output = Path(sys.argv[1])
    plain, image = output / 'plain', output / 'image'
    plain.mkdir(parents=True, exist_ok=True)
    image.mkdir(parents=True, exist_ok=True)
    base = load_mir_document(Path(__file__).parent / 'fixtures/tiny-after.json.gz')
    cases = []
    for name, status, debug, index in [
        ('failed-query', 'unsupported', False, '0'),
        ('supported-source', 'supported', False, '0'),
        ('debug-ancestor', 'unsupported', True, '0'),
        ('noncanonical-index', 'unsupported', False, '00'),
        ('missing-index', 'unsupported', False, '999999999999999999999999999'),
    ]:
        doc = copy.deepcopy(base)
        query = {'resolved': {'status': status}}
        if debug:
            query['status'] = 'debug_payload'
        doc['compiler_runtime_queries']['virtual'] = [query]
        doc['selected_scope']['retained_catalog_obligations'] = [
            {'path': f'compiler_runtime_queries.virtual[{index}].resolved', 'status': 'unsupported'}]
        cases.append((name, doc))
    for name, value in [
        ('argument-status', [{'kind': 'synthetic', 'status': 'unsupported'}]),
        ('argument-scalar', False),
        ('argument-region', [{'region': {'kind': 'synthetic', 'status': 'unsupported'}}]),
        ('argument-hard-error', [{'rvalue': {'kind': 'Use'}}]),
        ('argument-debug', [{'status': 'debug_payload', 'rvalue': {'kind': 'Use'}}]),
    ]:
        doc = copy.deepcopy(base)
        doc['synthetic'] = {'generic_args': value}
        cases.append((name, doc))
    for name, doc in cases:
        (image / f'{name}.json').write_text(json.dumps(encode(doc), separators=(',', ':')) + '\n')
        legacy = dict(doc, shared_payloads={'schema_version': 2, 'nodes': []})
        (plain / f'{name}.json').write_text(json.dumps(legacy, separators=(',', ':')) + '\n')
    print(f'{len(cases)} metadata reuse parity cases generated')


if __name__ == '__main__':
    main()
