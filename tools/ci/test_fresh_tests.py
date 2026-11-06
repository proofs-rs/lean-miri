"""Fresh-suite registration and strict same-snapshot reference admission."""
import json
from pathlib import Path
import tempfile
import unittest

import fresh_tests as fresh
import run as ci


class FreshTests(unittest.TestCase):
    def test_each_guest_and_metadata_check_is_an_independent_suite(self):
        suites = ci.suites('fresh')
        names = [suite.name for suite in suites]
        expected = ['query-demand', 'runtime-type-closure', 'vtable-cross-crate', *fresh.FOCUSED]
        self.assertEqual(names, ['build', 'fresh-prepare', *expected])
        for suite in suites[2:]:
            self.assertEqual(suite.command, ('python3', 'tools/ci/fresh_tests.py', suite.name))

    def test_reference_rejects_unrelated_failure_and_changed_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / 'input.json'
            output.write_bytes(b'{}')
            # FNV-1a identity of these exact two bytes.
            fingerprint = 0xcbf29ce484222325
            for byte in b'{}':
                fingerprint = ((fingerprint ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
            sidecar = {
                **{name + '_commit': (fresh.ROOT / f'upstream/.pins/{name}.commit').read_text().strip()
                   for name in ('rustc', 'miri')},
                'snapshot_byte_length': 2, 'snapshot_fnv1a64': f'{fingerprint:016x}',
                'reference': {'config': {'same_tcx': True}, 'status': 'failed',
                              'outcome': {'kind': 'miri_evaluation_error'}},
            }
            Path(str(output) + '.miri-reference.json').write_text(json.dumps(sidecar))
            output.with_suffix('.export.log').write_text('compiler panic')
            with self.assertRaises(AssertionError):
                fresh.reference_check(output, True)
            output.with_suffix('.export.log').write_text(
                'error: Undefined Behavior: uninitialized value\n\nsecondary: Data race')
            with self.assertRaises(AssertionError):
                fresh.reference_check(output, True)
            output.with_suffix('.export.log').write_text('error: Undefined Behavior: Data race detected')
            fresh.reference_check(output, True)
            output.write_bytes(b'changed')
            with self.assertRaises(AssertionError):
                fresh.reference_check(output, True)


if __name__ == '__main__':
    unittest.main()
