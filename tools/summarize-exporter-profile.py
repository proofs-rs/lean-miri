#!/usr/bin/env python3
"""Summarize LEAN_MIRI_PROFILE_EXPORT logs without double-counting nested spans.

Only direct-mode process-relative events can separate the rustc driver from its
export callback. Compiler queries inside the callback remain part of producer
spans; this report does not pretend those spans are pure query time.
"""
import argparse
from collections import defaultdict
import json
import math
from pathlib import Path


def summarize(text):
    spans = defaultdict(list)
    events = defaultdict(list)
    catalogs = []
    domains = []
    for line in text.splitlines():
        if line.startswith(('export_profile: ', 'export_profile_at: ')):
            kind, name, raw = line.split()
            value = float(raw)
            if not math.isfinite(value) or value < 0:
                raise ValueError('invalid exporter profile duration')
            (spans if kind == 'export_profile:' else events)[name].append(value)
        elif line.startswith(('export_catalog: ', 'export_domain: ')):
            parts = line.split()
            domain = parts[0] == 'export_domain:'
            row = {'phase': parts[1]} if domain else {}
            for field in (parts[2:] if domain else parts[1:]):
                name, raw = field.split('=', 1)
                value = int(raw)
                if value < 0 or name in row:
                    raise ValueError('invalid catalog count')
                row[name] = value
            (domains if domain else catalogs).append(row)
    if not spans:
        raise ValueError('no exporter profile spans')
    direct = {}
    if any(name.startswith('direct.') for name in events):
        def event(name):
            values = events.get(name, [])
            if len(values) != 1:
                raise ValueError(f'missing or repeated direct boundary: {name}')
            return values[0]
        start, enter, leave, end = (event(name) for name in
            ('direct.before_driver', 'analysis.enter', 'analysis.exit', 'direct.driver'))
        if not start <= enter <= leave <= end:
            raise ValueError('exporter profile boundaries out of order')
        direct = {'driver_before_callback': enter - start,
                  'export_callback': leave - enter,
                  'driver_after_callback': end - leave,
                  'driver_total': end - start}
    return {'span_seconds': {name: {'total': sum(values), 'calls': len(values), 'values': values}
                             for name, values in sorted(spans.items())},
            'direct_seconds': direct, 'catalog_rounds': catalogs, 'domain_snapshots': domains,
            'interpretation': 'Parent spans include children. Do not sum direct.driver, '
                'callback spans, or nested image/patch/scope/covariance spans together. '
                'Producer spans combine compiler queries and data construction.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    args = parser.parse_args()
    print(json.dumps(summarize(args.log.read_text()), indent=2))


if __name__ == '__main__':
    main()
