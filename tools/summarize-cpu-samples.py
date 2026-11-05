#!/usr/bin/env python3
"""Attribute interrupted PCs to ELF symbols; exclusive samples, never call stacks.

Usage: summarize-cpu-samples.py PREFIX [--phases MEASURE-RUN.json]
PREFIX.maps and PREFIX.samples are produced by cpu-sample.c. Outputs JSON.
Use --stack-depth 32 only for WITH_LIBUNWIND records. Linked code folding may
give shared helpers another specialization's name; use callers for attribution.
"""
import argparse
import bisect
from collections import Counter, defaultdict
import json
from functools import lru_cache
from pathlib import Path
import struct
import subprocess


def load_maps(path):
    mappings = []
    bases = {}
    for line in Path(path).read_text().splitlines():
        fields = line.split(maxsplit=5)
        if len(fields) != 6 or not fields[5].startswith('/'):
            continue
        span, permissions, offset, _, _, name = fields
        start, end = (int(x, 16) for x in span.split('-'))
        offset = int(offset, 16)
        # Use the ELF header mapping, not executable-map start minus file
        # offset: lld may add a page between LOAD segments (Lean/Rust PIEs do).
        if offset == 0:
            bases[name] = start
        if 'x' in permissions:
            mappings.append((start, end, name))
    return sorted(mappings), bases


def symbols(path):
    result = subprocess.run(['nm', '-n', '-S', '--defined-only', '--format=posix', path],
                            capture_output=True, text=True)
    if result.returncode or not result.stdout.strip():
        result = subprocess.run(['nm', '-D', '-n', '-S', '--defined-only', '--format=posix', path],
                                capture_output=True, text=True)
    rows = []
    for line in result.stdout.splitlines():
        fields = line.split()
        if len(fields) >= 3 and fields[1] in 'tTwWiI':
            rows.append((int(fields[2], 16), int(fields[3], 16) if len(fields) > 3 else 0, fields[0]))
    return sorted(rows)


def summarize(prefix, phases=None, leaf_spans=(), stack_depth=0):
    mappings, bases = load_maps(str(prefix) + '.maps')
    starts = [x[0] for x in mappings]
    tables = {}
    for _, _, path in mappings:
        if path in tables:
            continue
        header = subprocess.check_output(['readelf', '-h', path], text=True)
        dynamic = 'DYN ' in header
        if dynamic:
            loads = subprocess.check_output(['readelf', '-lW', path], text=True)
            headers = [line.split() for line in loads.splitlines() if line.strip().startswith('LOAD ')]
            if not any(int(row[1], 16) == 0 and int(row[2], 16) == 0 for row in headers):
                raise ValueError(f'unsupported nonzero ELF header address: {path}')
        rows = symbols(path)
        tables[path] = (dynamic, rows, [x[0] for x in rows])
    bounds = []
    if phases:
        events = json.loads(Path(phases).read_text())['events']
        bounds = [(events[a], events[b], name) for a, b, name in [
            ('decode_start', 'decode_end', 'decode'), ('lower_start', 'lower_end', 'lower'),
            ('prepare_start', 'prepare_end', 'prepare'),
            ('guest_start', 'bootstrap_ready', 'bootstrap'),
            ('bootstrap_ready', 'raw_result', 'guest')]
            if a in events and b in events]
        # Use only explicitly selected spans known to contain no nested
        # profiler spans. Reported exclusive times cannot bound parent calls.
        for span in json.loads(Path(phases).read_text()).get('internal_profile_spans', []):
            name = span['provider'] + '.' + span['name']
            if name in leaf_spans:
                end = span['wall_monotonic_ns']
                bounds.append((end - round(span['seconds'] * 1e9), end, 'leaf:' + name))
    @lru_cache(maxsize=None)
    def resolve_pc(pc):
        index = bisect.bisect_right(starts, pc) - 1
        name = '<unmapped>'
        if index >= 0:
            start, end, path = mappings[index]
            if pc < end:
                dynamic, rows, addresses = tables[path]
                if dynamic and path not in bases:
                    raise ValueError(f'no ELF header mapping: {path}')
                address = pc - bases[path] if dynamic else pc
                i = bisect.bisect_right(addresses, address) - 1
                name = Path(path).name + ':<no symbol>'
                if i >= 0 and rows[i][1] and address < rows[i][0] + rows[i][1]:
                    name = Path(path).name + ':' + rows[i][2]
        return name
    counts = defaultdict(Counter)
    cumulative = defaultdict(Counter)
    threads = Counter()
    raw = Path(str(prefix) + '.samples').read_bytes()
    width = 8 * (3 + stack_depth)
    if len(raw) % width:
        raise ValueError('truncated sample record')
    for record in struct.iter_unpack('<' + 'Q' * (3 + stack_depth), raw):
        timestamp, pc, thread, *callers = record
        threads[str(thread)] += 1
        name = resolve_pc(pc)
        # Return addresses point just past the call, possibly at a symbol end.
        chain = {name} | {resolve_pc(address - 1) for address in callers if address}
        selected = ['all'] + [phase for start, end, phase in bounds if start <= timestamp < end]
        for phase in selected:
            counts[phase][name] += 1
            cumulative[phase].update(chain)
    return {'sample_interval_cpu_seconds': .004, 'threads': dict(threads),
            'stack_depth': stack_depth,
            'kind': 'PC samples; cumulative callers only with explicit unwind mode; no speedup claim',
            'phases': {phase: {'samples': sum(rows.values()),
                'top': [{'symbol': name, 'samples': n, 'fraction': n / sum(rows.values())}
                        for name, n in rows.most_common(40)],
                'cumulative_top': [{'symbol': name, 'samples': n, 'fraction': n / sum(rows.values())}
                                   for name, n in cumulative[phase].most_common(60)]}
                for phase, rows in counts.items()}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('prefix', type=Path)
    parser.add_argument('--phases', type=Path)
    parser.add_argument('--leaf-span', action='append', default=[],
                        help='exact provider.name, containing no nested profiler calls')
    parser.add_argument('--stack-depth', type=int, choices=[0, 32], default=0)
    args = parser.parse_args()
    print(json.dumps(summarize(args.prefix, args.phases, args.leaf_span, args.stack_depth), indent=2))
