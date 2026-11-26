#!/usr/bin/env python3
"""Fresh no_std miri_start export, finite vtable sources and connected execution.

The default requires nonidentity source normalization consumed during execution. Named HRTB syntax alone is
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
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import pool_entry, decode_mir_document, inspection_document


def require_external_constant(document, name, compiler_mir):
    """Require a root constant whose allocation refers to a decoded vtable.

    Resolved MIR no longer retains unevaluated constant definition IDs. Check
    the pinned compiler's pre-evaluation MIR independently, then inspect the
    exported root's original allocation graph (never a prepared salt probe).
    This is a fixture-specific provenance control, not a general translation proof.
    """
    def walk(value):
        if isinstance(value, dict):
            yield value
            for item in value.values():
                yield from walk(item)
        elif isinstance(value, list):
            for item in value:
                yield from walk(item)

    root_mir = compiler_mir.split('fn miri_start(', 1)
    if len(root_mir) != 2:
        raise SystemExit('compiler MIR lacks miri_start')
    root_mir = root_mir[1].split('\n}')[0]
    if not re.search(r'\bconst ' + re.escape(name) + r'\s*;', root_mir):
        raise SystemExit(f'compiler root MIR lacks external constant: {name}')
    external_names = set(re.findall(r'\bconst ([A-Za-z_]\w*::[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*)', root_mir))
    external_names = {item for item in external_names if not item.startswith('miri_start::')}
    if external_names != {name}:
        raise SystemExit(f'ambiguous external constant origins: {sorted(external_names)}')
    if 'PointerCoercion(Unsize' in root_mir:
        raise SystemExit('cross-crate control unexpectedly constructs a local vtable')
    for root in document['body_roots']:
        if root['def_path'] != 'miri_start':
            continue
        body = pool_entry(document, 'bodies', root['body'])
        for constant in walk(body['basic_blocks']):
            if constant.get('kind') != 'evaluated_const':
                continue
            value = constant.get('value', {})
            if value.get('kind') != 'indirect_allocation':
                continue
            allocation = pool_entry(document, 'allocations', value['allocation'])
            for reference in allocation.get('relocations', []):
                target = pool_entry(document, 'allocations', reference['target'])
                if target.get('kind') == 'vtable':
                    print(f'vtable-erasure: external constant {name} -> symbolic vtable PASS')
                    return
    raise SystemExit(f'missing external constant with symbolic-vtable relocation: {name}')


def fingerprint(raw):
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    return f'{digest:016x}'


def summarize_queries(raw, query_log, runtime_log):
    """Join exact runtime keys to finite source material, never to an answer catalog."""
    document = json.loads(raw)
    types = document['types']
    predicates = document['compiler_predicate_queries']

    def normalize(key):
        ty, ids = key
        if type(ty) is not int or not 0 <= ty < len(types):
            raise ValueError('runtime key has no source type declaration')
        output = types[ty]['source_layout']['normalized_type']
        if not 0 <= output < len(types):
            raise ValueError('source normalization references an absent type')
        erased = []
        for predicate in ids:
            if type(predicate) is not int or not 0 <= predicate < len(predicates):
                raise ValueError('runtime key has no predicate source material')
            row = predicates[predicate]
            if row['predicate_id'] != predicate:
                raise ValueError('predicate source identity differs from its index')
            erased.append(row['erased'])
        return output, tuple(erased)

    def events(log, prefix):
        pattern = re.compile(r'^' + prefix + r' input_type=(\d+) input_predicates=#(\[[^\]]*\]) '
                             r'output_type=(\d+) output_predicates=#(\[[^\]]*\])$')
        for line in log.splitlines():
            if not line.startswith(prefix + ' '):
                continue
            match = pattern.fullmatch(line)
            if not match:
                raise ValueError('incomplete exact source query trace')
            before = int(match[1]), tuple(json.loads(match[2]))
            after = int(match[3]), tuple(json.loads(match[4]))
            if normalize(before) != after:
                raise ValueError('runtime result differs from its exact source key')
            yield before, after

    mappings = {}
    for before, after in events(query_log, 'vtable_source_map'):
        if before in mappings:
            raise ValueError('duplicate source key mapping')
        mappings[before] = after
    if not mappings:
        raise ValueError('no source key mappings: no coverage')
    counts = {}
    runtime_calls = runtime_nonidentity = 0
    for before, after in events(runtime_log, 'vtable_query'):
        runtime_calls += 1
        runtime_nonidentity += before != after
        counts[before] = counts.get(before, 0) + 1
    return {
        'schema': 'lean-miri-source-vtable-consumption-v1',
        'snapshot_fnv1a64': fingerprint(raw), 'snapshot_byte_length': len(raw),
        'rustc_commit': document['producer']['rustc_commit'],
        'source_keys': [{'input_type': before[0], 'input_predicates': list(before[1]),
                         'output_type': after[0], 'output_predicates': list(after[1]),
                         'nonidentity': before != after, 'runtime_calls': counts.get(before, 0)}
                        for before, after in mappings.items()],
        'runtime_calls': runtime_calls, 'runtime_nonidentity_calls': runtime_nonidentity,
        'nonidentity_source_keys': sum(before != after for before, after in mappings.items()),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path, help='new output under scratch/')
    parser.add_argument('--expect', choices=['identity', 'nonidentity'], default='nonidentity')
    parser.add_argument('--require-predicate-contrast', action='store_true',
                        help='require same-type query pairs with distinct input and output predicates')
    parser.add_argument('--require-lockstep', action='store_true',
                        help='require structural lockstep computation for distinct source supertraits')
    parser.add_argument('--require-trait-vptr', action='store_true',
                        help='require the shared-memory TraitVPtr control and its alias negative checks')
    parser.add_argument('--extern', action='append', default=[], metavar='NAME=RLIB',
                        help='dependency built with the pinned compiler and MIR-enabled sysroot')
    parser.add_argument('--require-external-constant', metavar='CRATE::CONST',
                        help='require a root external constant referring to a symbolic vtable')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/debug/lean-miri-mir-exporter')
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new file under scratch/')
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8eb778d04094'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/lake/miri-sysroot'))
    elan = Path(env.get('ELAN_HOME', ROOT / '.elan'))
    env['ELAN_HOME'] = str(elan)
    env['PATH'] = f"{toolchain / 'bin'}:{env.get('PATH', '')}"
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '1'
    env.pop('LEAN_MIRI_REFERENCE_ARGS_JSON', None)
    env['LEAN_NUM_THREADS'] = '1'
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
        # Reuse every rustc flag and dependency from this exact export. Only the
        # output mode changes; no MIR evaluation or exporter data is fabricated.
        mir_path = output.with_suffix('.compiler.mir')
        rustc_cmd = [str(toolchain / 'bin/rustc'), *cmd[cmd.index('--') + 1:],
                     '--emit=mir', '-o', str(mir_path)]
        subprocess.run(rustc_cmd, cwd=ROOT, env=env, check=True, timeout=args.timeout)
        require_external_constant(inspection_document(decode_mir_document(json.loads(raw))), args.require_external_constant, mir_path.read_text())
    query_args = [args.expect] + (['predicate-contrast'] if args.require_predicate_contrast else [])
    if args.require_trait_vptr:
        query_args.append('trait-vptr')
    query_args.append('trace-map')
    subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run',
                    'tests/input/SourceUpcastQueries.lean', str(output),
                    *([] if args.require_lockstep else ['no-upcast'])],
                   cwd=ROOT, env=env, check=True, timeout=args.timeout)
    logs = []
    for harness, extra in [('tests/input/VTableErasureQuery.lean', query_args),
                           ('tests/connected/203-upcast-a-prefix.lean', ['--trace-vtable-queries'])]:
        log_path = output.with_suffix(f'.consumer-{len(logs)}.log')
        with log_path.open('x') as log:
            subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run', harness,
                            str(output), *extra], cwd=ROOT, env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
        logs.append(log_path.read_text())
        print(logs[-1], end='')
    if output.read_bytes() != raw:
        raise SystemExit('input bytes changed during consumer validation')
    summary = summarize_queries(raw, *logs)
    if args.expect == 'nonidentity' and summary['runtime_nonidentity_calls'] == 0:
        raise SystemExit('nonidentity source normalization was not consumed by the connected runtime')
    summary_path = output.with_suffix('.vtable-consumption.json')
    with summary_path.open('x') as report:
        json.dump(summary, report, indent=2)
    print(f"vtable-erasure: runtime calls={summary['runtime_calls']}; "
          f"runtime nonidentity calls={summary['runtime_nonidentity_calls']}")
    print(f'vtable-erasure: reference exit_zero + connected exit_zero; expectation={args.expect}')


if __name__ == '__main__':
    main()
