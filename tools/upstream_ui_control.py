"""Private runner control transport; guest streams are never protocol inputs.

The caller owns a fresh regular file and passes only its descriptor to the
runner. JSONL is deliberately strict: partial, ambiguous or unbound output is
not evidence of a guest outcome. This module grants no guest file capability.
"""
from contextlib import contextmanager
import json
import os
import stat

VERSION = 1
UI_CHOICE_MODE = 'seeded-diagnostic seed=0 algorithm=SplitMix64-v1'
HEADER_FIELDS = {'run_id', 'snapshot_fnv1a64', 'snapshot_byte_length',
                 'source', 'runtime_flags', 'choice_mode'}
RECORD_FIELDS = {'version', 'sequence', 'kind', 'payload'}


class ControlProtocolError(ValueError):
    pass


@contextmanager
def control_file(path):
    """Own exactly one parent FD on every success/failure path, never reopen it."""
    descriptor = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR | os.O_CLOEXEC, 0o600)
    try:
        if descriptor < 3:
            import fcntl
            moved = fcntl.fcntl(descriptor, fcntl.F_DUPFD_CLOEXEC, 3)
            os.close(descriptor)
            descriptor = moved
        os.fchmod(descriptor, 0o600)
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise ControlProtocolError('control descriptor is not a regular file')
        yield descriptor
    finally:
        os.close(descriptor)


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ControlProtocolError('duplicate JSON object key')
        result[key] = value
    return result


def _nonfinite(_):
    raise ControlProtocolError('nonfinite JSON number')


PROFILE_BOOL_FIELDS = {
    'data_race_detector', 'weak_memory_emulation', 'fixed_scheduling', 'ignore_leaks',
    'collect_leak_backtraces', 'genmc', 'short_fd_operations', 'float_nondeterminism'}
PROFILE_FIELDS = PROFILE_BOOL_FIELDS | {
    'num_cpus', 'environment_policy', 'argv0', 'rng_seed', 'choice_policy',
    'borrow_tracker', 'tree_borrows', 'validation', 'alignment_check', 'provenance_mode',
    'native_libraries', 'cmpxchg_weak_failure_rate', 'address_reuse_cross_thread_rate'}
FRAME_RAW_FIELDS = {'raw_file', 'raw_line', 'raw_end_line', 'raw_column',
                    'lo', 'hi', 'body_id', 'span_id'}
FRAME_SHARED_FIELDS = {'location_mode', 'file', 'line', 'column'}


def _natural(value):
    return type(value) is int and value >= 0


def _validate_profile(profile):
    if not isinstance(profile, dict) or set(profile) != PROFILE_FIELDS:
        raise ControlProtocolError('invalid profile fields')
    if any(type(profile[name]) is not bool for name in PROFILE_BOOL_FIELDS):
        raise ControlProtocolError('invalid profile boolean')
    if (not _natural(profile['num_cpus']) or not _natural(profile['native_libraries']) or
            not _natural(profile['rng_seed']) or profile['rng_seed'] >= 2**64 or
            not isinstance(profile['argv0'], str)):
        raise ControlProtocolError('invalid profile scalar')
    for name, allowed in (
            ('environment_policy', ('empty',)), ('choice_policy', ('seeded-generated-0',)),
            ('borrow_tracker', ('tree_borrows', 'none')), ('validation', ('No', 'Shallow', 'Deep')),
            ('alignment_check', ('None', 'Int', 'Symbolic')),
            ('provenance_mode', ('Default', 'Strict', 'Permissive'))):
        if profile[name] not in allowed:
            raise ControlProtocolError('unknown profile enum')
    tree = profile['tree_borrows']
    if tree is not None and (not isinstance(tree, dict) or
            set(tree) != {'precise_interior_mut', 'implicit_writes'} or
            any(type(value) is not bool for value in tree.values())):
        raise ControlProtocolError('invalid tree-borrows profile')
    for name in ('cmpxchg_weak_failure_rate', 'address_reuse_cross_thread_rate'):
        if type(profile[name]) not in (int, float) or not 0 <= profile[name] <= 1:
            raise ControlProtocolError('invalid profile probability')


def _validate_terminal(terminal):
    required = {'kind', 'detail', 'frames'}
    if (not isinstance(terminal, dict) or not required <= set(terminal) or
            set(terminal) - required - {'allocation_backtraces'}):
        raise ControlProtocolError('invalid terminal fields')
    if terminal['kind'] not in ('exit', 'ub', 'unsupported', 'failed', 'pending'):
        raise ControlProtocolError('unknown terminal enum')
    if not isinstance(terminal['detail'], str) or not isinstance(terminal['frames'], list):
        raise ControlProtocolError('invalid terminal payload')
    for frame in terminal['frames']:
        if frame is None:
            continue
        if not isinstance(frame, dict):
            raise ControlProtocolError('invalid terminal frame')
        mode = frame.get('location_mode')
        if mode == 'compiler_hygiene':
            fields = FRAME_RAW_FIELDS | FRAME_SHARED_FIELDS | {'collapsed_lo'}
        elif mode == 'raw_span_no_exact_hygiene':
            fields = FRAME_RAW_FIELDS | FRAME_SHARED_FIELDS | {'end_line'}
        else:
            raise ControlProtocolError('unknown frame location mode')
        if set(frame) != fields:
            raise ControlProtocolError('invalid frame fields')
        for name, value in frame.items():
            if name in ('raw_file', 'file'):
                if value is not None and not isinstance(value, str):
                    raise ControlProtocolError('invalid frame filename')
            elif name == 'location_mode':
                pass
            elif name == 'span_id' and value is None:
                pass
            elif not _natural(value):
                raise ControlProtocolError('invalid frame number')
    traces = terminal.get('allocation_backtraces', [])
    if not isinstance(traces, list):
        raise ControlProtocolError('invalid allocation backtraces')
    for trace in traces:
        if (not isinstance(trace, dict) or set(trace) != {'allocation_id', 'frames'} or
                not _natural(trace['allocation_id']) or not isinstance(trace['frames'], list)):
            raise ControlProtocolError('invalid allocation backtrace')
        for frame in trace['frames']:
            if (not isinstance(frame, dict) or set(frame) != {'instance_id', 'span_id'} or
                    any(not _natural(value) for value in frame.values())):
                raise ControlProtocolError('invalid allocation backtrace frame')


def parse_control(lines, expected_header):
    """Consume binary JSONL incrementally; discard boundary payloads after validation."""
    if set(expected_header) != HEADER_FIELDS:
        raise ControlProtocolError('invalid expected control binding')
    profile = terminal = header = None
    sequence = 0
    for raw in lines:
        if not isinstance(raw, bytes) or not raw.endswith(b'\n'):
            raise ControlProtocolError('truncated control record')
        try:
            record = json.loads(raw.decode('utf-8'), object_pairs_hook=_unique_object,
                                parse_constant=_nonfinite)
        except (UnicodeError, ValueError, RecursionError) as error:
            raise ControlProtocolError('invalid control JSON') from error
        if not isinstance(record, dict) or set(record) != RECORD_FIELDS:
            raise ControlProtocolError('invalid control record fields')
        if type(record['version']) is not int or record['version'] != VERSION:
            raise ControlProtocolError('unsupported control version')
        if type(record['sequence']) is not int or record['sequence'] != sequence:
            raise ControlProtocolError('noncontiguous control sequence')
        if terminal is not None:
            raise ControlProtocolError('record after terminal')
        kind, payload = record['kind'], record['payload']
        if sequence == 0 and kind != 'header':
            raise ControlProtocolError('missing initial control header')
        if kind == 'header':
            if sequence != 0 or not isinstance(payload, dict) or set(payload) != HEADER_FIELDS:
                raise ControlProtocolError('invalid or duplicate control header')
            if (type(payload['snapshot_fnv1a64']) is not int or
                    not 0 <= payload['snapshot_fnv1a64'] < 2**64 or
                    type(payload['snapshot_byte_length']) is not int or
                    payload['snapshot_byte_length'] < 0 or
                    not isinstance(payload['run_id'], str) or
                    len(payload['run_id']) != 32 or
                    any(char not in '0123456789abcdef' for char in payload['run_id']) or
                    not isinstance(payload['source'], str) or
                    not isinstance(payload['runtime_flags'], list) or
                    any(not isinstance(flag, str) for flag in payload['runtime_flags']) or
                    not isinstance(payload['choice_mode'], str)):
                raise ControlProtocolError('invalid control header types')
            if payload != expected_header:
                raise ControlProtocolError('control header binding mismatch')
            header = payload
        elif kind == 'boundary':
            if not isinstance(payload, str):
                raise ControlProtocolError('invalid boundary payload')
        elif kind == 'profile':
            if profile is not None or not isinstance(payload, dict):
                raise ControlProtocolError('invalid or duplicate profile')
            _validate_profile(payload)
            profile = payload
        elif kind == 'terminal':
            if (profile is None or not isinstance(payload, dict) or
                    not isinstance(payload.get('kind'), str) or
                    not isinstance(payload.get('detail'), str)):
                raise ControlProtocolError('terminal requires one prior profile and typed outcome')
            _validate_terminal(payload)
            terminal = payload
        else:
            raise ControlProtocolError('unknown control record kind')
        sequence += 1
    if header is None or profile is None or terminal is None:
        raise ControlProtocolError('incomplete control protocol')
    return {'header': header, 'profile': profile, 'terminal': terminal, 'records': sequence}


def read_control(descriptor, expected_header):
    os.lseek(descriptor, 0, os.SEEK_SET)
    # A duplicate lets the buffered reader close its own handle while preserving
    # the caller's lifetime. No path lookup or stdout/stderr fallback occurs.
    with os.fdopen(os.dup(descriptor), 'rb') as stream:
        return parse_control(stream, expected_header)
