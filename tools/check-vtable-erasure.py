#!/usr/bin/env python3
"""Fresh no_std miri_start export, exact vtable queries and connected execution.

The default requires a nonidentity compiler result. Named HRTB syntax alone is
not evidence: PostAnalysisNormalize already erases/anonymizes successful
MIR type queries; lockstep tail normalization also applies when traversing fields.
Use --expect identity explicitly for the retained negative controls.
"""
import argparse
import json
import os
import re
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def require_external_constant(document, name):
    """Require a root constant whose allocation refers to a decoded vtable.

    Inspect the original exported graph, not one of the salt probes created by
    prepared allocation closure. The Lean checks still consume the original bytes.
    """
    def expand(value):
        if isinstance(value, dict):
            if set(value) == {'$lean_miri_shared_ref'}:
                return expand(document['shared_payloads']['nodes'][value['$lean_miri_shared_ref']])
            return {key: expand(item) for key, item in value.items()}
        if isinstance(value, list):
            return [expand(item) for item in value]
        return value

    def walk(value):
        if isinstance(value, dict):
            yield value
            for item in value.values():
                yield from walk(item)
        elif isinstance(value, list):
            for item in value:
                yield from walk(item)

    allocations = {row['allocation_id']: row for row in expand(document['allocations'])}
    for body in expand(document['bodies']):
        if body.get('def_path') != 'miri_start':
            continue
        for constant in walk(body['basic_blocks']):
            source = constant.get('source', {})
            if (constant.get('kind') != 'evaluated_const' or source.get('def_path') != name or
                    source.get('def_id', {}).get('crate', 0) == 0):
                continue
            value = constant.get('value', {})
            if value.get('kind') != 'indirect_allocation':
                continue
            allocation = allocations[value['allocation']['allocation_id']]
            for reference in walk(allocation):
                target = reference.get('target', {}).get('allocation_id')
                if allocations.get(target, {}).get('kind') == 'vtable':
                    print(f'vtable-erasure: external constant {name} -> symbolic vtable PASS')
                    return
    raise SystemExit(f'missing external constant with symbolic-vtable relocation: {name}')


def fingerprint(raw):
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    return f'{digest:016x}'


def summarize_queries(raw, provenance, query_log, runtime_log):
    """Join producer rows to actual lookups; catalog presence is not consumption."""
    def expand(value):
        if isinstance(value, dict):
            if set(value) == {'$lean_miri_shared_ref'}:
                return expand(document['shared_payloads']['nodes'][value['$lean_miri_shared_ref']])
            return {key: expand(item) for key, item in value.items()}
        if isinstance(value, list):
            return [expand(item) for item in value]
        return value

    def events(log, prefix):
        for line in log.splitlines():
            if line.startswith(prefix + ' '):
                fields = dict(re.findall(r'(\w+)=(\d+)', line))
                if 'missing' in line:
                    raise ValueError('runtime lookup has no compiler query identity')
                yield {key: int(value) for key, value in fields.items()}

    if provenance['schema'] != 'lean-miri-vtable-origins-v1':
        raise ValueError('unknown vtable provenance schema')
    document = json.loads(raw)
    if (provenance['snapshot_fnv1a64'] != fingerprint(raw) or
            provenance['snapshot_byte_length'] != len(raw) or
            provenance['rustc_commit'] != expand(document['producer'])['rustc_commit']):
        raise ValueError('producer provenance belongs to different input bytes/compiler')
    rows = expand(document['compiler_vtable_queries'])
    catalog = {row['query_id']: row for row in rows}
    origins = {row['query_id']: row for row in provenance['queries']}
    if len(catalog) != len(rows) or len(origins) != len(provenance['queries']) or catalog.keys() != origins.keys():
        raise ValueError('missing/duplicate producer query provenance')
    mappings = {}
    for event in events(query_log, 'vtable_query_map'):
        query_id = event['query_id']
        if query_id in mappings or query_id not in catalog:
            raise ValueError('unknown/duplicate consumer query mapping')
        mappings[query_id] = event
    if mappings.keys() != catalog.keys():
        raise ValueError('consumer query mapping is incomplete')
    result = []
    for query_id, row in sorted(catalog.items()):
        origin = origins[query_id]
        before = (row['input_type']['type_id'], [p['predicate_id'] for p in row['input_predicates']])
        after = (row['output_type']['type_id'], [p['predicate_id'] for p in row['output_predicates']])
        if (origin['input_type_id'], origin['input_predicate_ids']) != before or not origin['origins']:
            raise ValueError('producer provenance differs from complete query key')
        if any(o.get('parent_query_id') is not None and o['parent_query_id'] not in catalog
               for o in origin['origins']):
            raise ValueError('producer parent query is not closed')
        mapping = mappings[query_id]
        if mapping['input_type'] != before[0] or mapping['output_type'] != after[0]:
            raise ValueError('consumer type mapping differs from compiler key')
        token_identity = (mapping['input_type'], mapping['input_token']) == (mapping['output_type'], mapping['output_token'])
        if token_identity != (before == after):
            raise ValueError('consumer predicate identity differs from compiler key')
        result.append({'query_id': query_id, 'nonidentity': before != after,
                       'runtime_calls': 0, 'origins': origin['origins']})
    results = {row['query_id']: row for row in result}
    for event in events(runtime_log, 'vtable_query'):
        query_id = event['query_id']
        if query_id not in mappings or any(event[key] != mappings[query_id][key] for key in ('input_type', 'input_token')):
            raise ValueError('runtime lookup does not match its exact consumer key')
        results[query_id]['runtime_calls'] += 1
    return {'queries': result, 'runtime_calls': sum(row['runtime_calls'] for row in result),
            'runtime_nonidentity_calls': sum(row['runtime_calls'] for row in result if row['nonidentity']),
            'nonidentity_catalog_queries': sum(row['nonidentity'] for row in result)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path, help='new output under scratch/')
    parser.add_argument('--trace-queries', action='store_true',
                        help='retain producer origins and exact runtime query consumption')
    parser.add_argument('--expect', choices=['identity', 'nonidentity'], default='nonidentity')
    parser.add_argument('--require-predicate-contrast', action='store_true',
                        help='require same-type query pairs with distinct input and output predicates')
    parser.add_argument('--require-trait-vptr', action='store_true',
                        help='require the shared-memory TraitVPtr control and its alias negative checks')
    parser.add_argument('--extern', action='append', default=[], metavar='NAME=RLIB',
                        help='dependency built with the pinned compiler and MIR-enabled sysroot')
    parser.add_argument('--require-external-constant', metavar='CRATE::CONST',
                        help='require a root external constant referring to a symbolic vtable')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/debug/lean-miri-mir-exporter')
    args = parser.parse_args()
    # A changed catalog row alone cannot establish execution of that branch.
    args.trace_queries = args.trace_queries or args.expect == 'nonidentity'
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new file under scratch/')
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    elan = Path(env.get('ELAN_HOME', ROOT / '.elan'))
    env['ELAN_HOME'] = str(elan)
    env['PATH'] = f"{toolchain / 'bin'}:{env.get('PATH', '')}"
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '1'
    env.pop('LEAN_MIRI_REFERENCE_ARGS_JSON', None)
    env['LEAN_NUM_THREADS'] = '1'
    provenance_path = output.with_suffix('.vtable-origins.json')
    env.pop('LEAN_MIRI_VTABLE_DIAGNOSTICS', None)
    if args.trace_queries:
        env['LEAN_MIRI_VTABLE_DIAGNOSTICS'] = str(provenance_path)
    cmd = [str(args.exporter.resolve()), '--output', str(output), '--root', 'miri_start', '--',
           str(args.source.resolve()), '--crate-type=bin', '--crate-name=vtable_erasure',
           '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir',
           '--cfg=miri', '--sysroot', str(sysroot)]
    for dependency in args.extern:
        cmd.extend(['--extern', dependency])
    with output.with_suffix('.export.log').open('x') as log:
        subprocess.run(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    reference = json.loads(Path(str(output) + '.miri-reference.json').read_text())
    raw = output.read_bytes()
    digest = fingerprint(raw)
    if (reference.get('status') != 'completed' or
            reference.get('rustc_commit') != (ROOT / 'upstream/.pins/rustc.commit').read_text().strip() or
            reference.get('miri_commit') != (ROOT / 'upstream/.pins/miri.commit').read_text().strip() or
            reference.get('reference', {}).get('status') != 'completed' or
            reference['reference'].get('outcome') != {'kind': 'exit_zero'} or
            reference['reference'].get('config', {}).get('same_tcx') is not True or
            reference.get('snapshot_byte_length') != len(raw) or
            reference.get('snapshot_fnv1a64') != digest):
        raise SystemExit('reference did not establish same-TyCtxt exit_zero for these exact bytes')
    if args.require_external_constant:
        require_external_constant(json.loads(raw), args.require_external_constant)
    query_args = [args.expect] + (['predicate-contrast'] if args.require_predicate_contrast else [])
    if args.require_trait_vptr:
        query_args.append('trait-vptr')
    if args.trace_queries:
        query_args.append('trace-map')
    logs = []
    for harness, extra in [('tests/input/VTableErasureQuery.lean', query_args),
                           ('tests/connected/203-upcast-a-prefix.lean', ['--trace-vtable-queries'] if args.trace_queries else [])]:
        log_path = output.with_suffix(f'.consumer-{len(logs)}.log')
        with log_path.open('x') as log:
            subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run', harness,
                            str(output), *extra], cwd=ROOT, env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        logs.append(log_path.read_text())
        print(logs[-1], end='')
    if output.read_bytes() != raw:
        raise SystemExit('input bytes changed during consumer validation')
    if args.trace_queries:
        summary = summarize_queries(raw, json.loads(provenance_path.read_text()), *logs)
        if args.expect == 'nonidentity' and summary['runtime_nonidentity_calls'] == 0:
            raise SystemExit('nonidentity catalog query was not consumed by the connected runtime')
        summary_path = output.with_suffix('.vtable-consumption.json')
        with summary_path.open('x') as report:
            json.dump(summary, report, indent=2)
        print(f"vtable-erasure: runtime calls={summary['runtime_calls']}; "
              f"runtime nonidentity calls={summary['runtime_nonidentity_calls']}")
    print(f'vtable-erasure: reference exit_zero + connected exit_zero; expectation={args.expect}')


if __name__ == '__main__':
    main()
