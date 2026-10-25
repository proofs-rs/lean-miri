#!/usr/bin/env python3
"""Summarize sampled outer scheduler progress from measure.py output.

Timing spans include scheduling and callbacks, and omit iterations below the
profiling threshold. Counts are observed boundaries, not MIR instruction counts. An unmatched sampled
before boundary does not identify a stuck iteration: later unsampled iterations
may have run. No progress summary establishes completion or safety.
"""
import argparse
import json
import pathlib
import re


def summarize(run):
    end = run.get('events', {}).get('guest_end')
    records = []
    timings = []
    for item in run.get('internal_profile_spans', []):
        if item.get('provider') != 'execution':
            continue
        if end is not None and item['wall_monotonic_ns'] >= end:
            continue
        timed = re.fullmatch(r'iteration_(\d+)\.(.*)', item['name'])
        if timed:
            timings.append({'iteration': int(timed[1]), 'starting_state': timed[2],
                            'seconds': item['seconds']})
            continue
        match = re.fullmatch(r'(before|after)\.iteration_(\d+)\.(.*)', item['name'])
        if match:
            records.append({
                'boundary': match[1], 'iteration': int(match[2]),
                'state': match[3], 'wall_monotonic_ns': item['wall_monotonic_ns'],
            })
    completed = [r['iteration'] + 1 for r in records if r['boundary'] == 'after']
    bootstrap = run.get('events', {}).get('bootstrap_ready')
    if records and bootstrap is not None:
        for record in records:
            record['seconds_since_bootstrap'] = (record['wall_monotonic_ns'] - bootstrap) / 1e9
    return {
        'timed_iteration_count': len(timings),
        'reported_iteration_seconds_sum': sum(t['seconds'] for t in timings),
        'slowest_outer_iterations': sorted(timings, key=lambda t: t['seconds'], reverse=True)[:10],
        'sampled_boundary_count': len(records),
        'completed_outer_iterations_lower_bound': max(completed, default=0),
        'first_sample': records[0] if records else None,
        'last_sample': records[-1] if records else None,
        'last_samples': records[-12:],
        'process_finalized_exit_observed': run.get('finalized_exit_observed', False),
        'raw_result_kind': run.get('raw_result_kind'),
        'caveat': 'Sampled scheduler boundaries; not a MIR instruction count or safety verdict.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run_json', type=pathlib.Path)
    args = parser.parse_args()
    run = json.loads(args.run_json.read_text())
    print(json.dumps(summarize(run), indent=2))


if __name__ == '__main__':
    main()
