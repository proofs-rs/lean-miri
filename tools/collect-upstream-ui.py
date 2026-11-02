#!/usr/bin/env python3
"""Require complete, non-overlapping coverage from all upstream UI shards."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
from suite import discover, source_fingerprint


def collect(root, expected, shard_count, fingerprint):
    records, errors, shards = [], [], set()
    result_files = sorted(root.rglob('results.jsonl'))
    for path in result_files:
        try:
            provenance = json.loads(path.with_name('provenance.json').read_text())
            index = provenance['shard_index']
            if provenance['project_source_sha256'] != fingerprint:
                errors.append(f'{path}: incompatible project source identity')
            if provenance['shard_count'] != shard_count or not 0 <= index < shard_count or index in shards:
                errors.append(f'{path}: invalid or duplicate shard {index}')
            shards.add(index)
            rows = [json.loads(line) for line in path.read_text().splitlines() if line]
            records.extend(rows)
            summary = json.loads(path.with_name('summary.json').read_text())
            if summary != dict(Counter(row['status'] for row in rows)):
                errors.append(f'{path}: summary does not match outcomes')
        except (OSError, ValueError, KeyError, TypeError) as error:
            errors.append(f'{path}: incomplete/invalid shard: {error}')
    observed = Counter(row['id'] for row in records)
    missing = sorted(set(expected) - observed.keys())
    unknown = sorted(observed.keys() - set(expected))
    duplicates = sorted(key for key, count in observed.items() if count != 1)
    if missing or unknown or duplicates or len(shards) != shard_count:
        errors.append('inventory/shard coverage is incomplete or overlapping')
    for row in records:
        if row['id'] in expected and row.get('reasons') != expected[row['id']]:
            errors.append(f'{row["id"]}: profile disposition changed')
        if row['id'] in expected and bool(expected[row['id']]) != (row['status'] == 'profile_unsupported'):
            errors.append(f'{row["id"]}: invalid unsupported disposition')
    counts = dict(Counter(row['status'] for row in records))
    complete = not errors
    return {'complete': complete, 'passed': complete and bool(counts.get('passed')) and
            all(row['status'] in ('passed', 'profile_unsupported') for row in records),
            'counts': counts, 'expected_cases': len(expected), 'observed_cases': len(records),
            'shards': sorted(shards), 'missing': missing, 'unknown': unknown,
            'duplicates': duplicates, 'errors': errors,
            'failures': [{'id': row['id'], 'status': row['status']} for row in records
                         if row['status'] not in ('passed', 'profile_unsupported')]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifacts', type=Path)
    parser.add_argument('--shards', type=int, default=32)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = collect(args.artifacts, {case.id: case.reasons for case in discover()},
                     args.shards, source_fingerprint())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('complete', 'passed', 'counts', 'expected_cases', 'observed_cases')}))
    return int(not report['passed'])


if __name__ == '__main__':
    raise SystemExit(main())
