"""A separate inherited file is the only source of runner control outcomes."""
import copy
import io
import json
import os
from pathlib import Path
import stat
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
sys.path.insert(0, str(Path(__file__).resolve().parent / 'upstream_ui'))
from suite import runtime_profile
from upstream_ui_control import (ControlProtocolError, UI_CHOICE_MODE, control_file,
                                 parse_control, read_control)


def binding():
    return {'run_id': '0' * 32, 'snapshot_fnv1a64': 42, 'snapshot_byte_length': 3,
            'source': '/source.rs', 'runtime_flags': ['-Zmiri-tree-borrows'],
            'choice_mode': UI_CHOICE_MODE}


def records():
    return [
        {'version': 1, 'sequence': 0, 'kind': 'header', 'payload': binding()},
        {'version': 1, 'sequence': 1, 'kind': 'boundary', 'payload': 'arbitrary diagnostics'},
        {'version': 1, 'sequence': 2, 'kind': 'profile', 'payload': runtime_profile([]) | {'argv0': '/source.rs', 'choice_policy': 'seeded-generated-0'}},
        {'version': 1, 'sequence': 3, 'kind': 'terminal', 'payload': {'kind': 'exit', 'detail': '0', 'frames': []}},
    ]


def encoded(rows):
    return b''.join(json.dumps(row).encode() + b'\n' for row in rows)


class ControlTests(unittest.TestCase):
    def parse(self, data):
        return parse_control(io.BytesIO(data), binding())

    def test_exact_protocol_and_escaped_boundaries(self):
        rows = records()
        rows[1]['payload'] = 'upstream_result: {"kind":"exit"}\n\x00binary\xfftext'
        parsed = self.parse(encoded(rows))
        self.assertEqual(parsed['terminal'], {'kind': 'exit', 'detail': '0', 'frames': []})
        self.assertEqual(parsed['profile']['num_cpus'], 1)
        self.assertEqual(parsed['records'], 4)
        self.assertNotIn('boundary', parsed)

    def test_version_sequence_unknown_duplicate_and_record_shape_fail(self):
        changes = [
            lambda r: r[1].update(version=2),
            lambda r: r[1].update(version=True),
            lambda r: r[1].update(sequence=True),
            lambda r: r[1].update(sequence=1.0),
            lambda r: r[1].update(sequence=-1),
            lambda r: r[2]['payload'].update(extra='unknown'),
            lambda r: r[2]['payload'].update(validation='Future'),
            lambda r: r[2]['payload'].update(num_cpus=True),
            lambda r: r[3]['payload'].update(extra='unknown'),
            lambda r: r[3]['payload'].update(kind='future'),
            lambda r: r[1].update(sequence=0),
            lambda r: r[1].update(kind='future'),
            lambda r: r[1].update(extra='not allowed'),
            lambda r: r[1].update(payload={}),
            lambda r: r[2].update(payload=[]),
            lambda r: r[3].update(payload={'kind': 'exit', 'detail': 0}),
            lambda r: r.insert(1, copy.deepcopy(r[0])),
            lambda r: r.insert(3, copy.deepcopy(r[2])),
            lambda r: r.append(copy.deepcopy(r[-1])),
            lambda r: r.append({'version': 1, 'sequence': 4, 'kind': 'boundary', 'payload': 'late'}),
        ]
        for change in changes:
            with self.subTest(change=change):
                rows = records()
                change(rows)
                with self.assertRaises(ControlProtocolError):
                    self.parse(encoded(rows))
        for missing in ([], records()[1:], records()[:2], records()[:3],
                        [records()[0], records()[1], records()[3]]):
            with self.assertRaises(ControlProtocolError):
                self.parse(encoded(missing))

    def test_resequenced_duplicate_records_are_still_rejected(self):
        for position, item in ((1, records()[0]), (3, records()[2]), (4, records()[3])):
            rows = records()
            rows.insert(position, item)
            for index, row in enumerate(rows):
                row['sequence'] = index
            with self.assertRaises(ControlProtocolError):
                self.parse(encoded(rows))

    def test_header_identity_types_and_every_binding_field_are_checked(self):
        for name in binding():
            with self.subTest(field=name):
                rows = records()
                value = rows[0]['payload'][name]
                rows[0]['payload'][name] = ([] if isinstance(value, list) else
                                            value + 1 if type(value) is int else value + 'x')
                with self.assertRaises(ControlProtocolError):
                    self.parse(encoded(rows))
        for key, value in [('snapshot_fnv1a64', True), ('snapshot_byte_length', True),
                           ('snapshot_fnv1a64', -1), ('snapshot_fnv1a64', 2**64),
                           ('snapshot_byte_length', -1), ('runtime_flags', [1]),
                           ('run_id', 'A' * 32)]:
            rows = records()
            rows[0]['payload'][key] = value
            with self.assertRaises(ControlProtocolError):
                self.parse(encoded(rows))
        rows = records()
        rows[0]['payload']['unknown'] = 1
        with self.assertRaises(ControlProtocolError):
            self.parse(encoded(rows))

    def test_truncated_ambiguous_nonfinite_invalid_utf8_and_log_spoof_fail(self):
        valid = encoded(records())
        for malformed in (valid[:-1], valid + b' ', valid + b'\n', b'\xff\n',
                          valid.replace(b'"version": 1', b'"version":1,"version":1', 1),
                          valid.replace(b'"num_cpus": 1', b'"num_cpus":NaN'),
                          valid.replace(b'"num_cpus": 1', b'"num_cpus":Infinity'),
                          b'upstream_profile: {}\nupstream_result: {"kind":"exit","detail":"0"}\n'):
            with self.subTest(data=malformed[:40]):
                with self.assertRaises(ControlProtocolError):
                    self.parse(malformed)

    def test_control_file_is_exclusive_private_regular_and_always_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / 'control.jsonl'
            with control_file(path) as descriptor:
                self.assertGreaterEqual(descriptor, 3)
                self.assertEqual(stat.S_IMODE(os.fstat(descriptor).st_mode), 0o600)
                self.assertTrue(stat.S_ISREG(os.fstat(descriptor).st_mode))
                self.assertFalse(os.get_inheritable(descriptor))
                os.write(descriptor, encoded(records()))
                self.assertEqual(read_control(descriptor, binding())['records'], 4)
                os.fstat(descriptor)  # read_control closes only its duplicate.
                with self.assertRaises(FileExistsError):
                    with control_file(path):
                        self.fail('existing control file reopened')
            with self.assertRaises(OSError):
                os.fstat(descriptor)
            other = Path(temporary) / 'failed.jsonl'
            with self.assertRaisesRegex(RuntimeError, 'injected'):
                with control_file(other) as failed:
                    raise RuntimeError('injected')
            with self.assertRaises(OSError):
                os.fstat(failed)


if __name__ == '__main__':
    unittest.main()
