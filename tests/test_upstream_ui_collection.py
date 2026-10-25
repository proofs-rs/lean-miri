"""Incomplete shards and unrelated subprocess failures cannot become coverage."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
from suite import discover, runtime_profile


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'tools' / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


collector = load('upstream_ui_collector', 'collect-upstream-ui.py')
driver = load('upstream_ui_driver', 'check-upstream-ui.py')


class CollectionTests(unittest.TestCase):
    def shard(self, root, index, rows):
        directory = root / str(index)
        directory.mkdir()
        (directory / 'provenance.json').write_text(json.dumps({
            'shard_index': index, 'shard_count': 2, 'project_source_sha256': 'pin'}))
        (directory / 'results.jsonl').write_text(''.join(json.dumps(r) + '\n' for r in rows))
        (directory / 'summary.json').write_text(json.dumps(dict(collector.Counter(r['status'] for r in rows))))
        return directory

    def test_complete_inventory_is_distinct_from_success(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            expected = {'a': [], 'b': ['setting unsupported']}
            a = self.shard(root, 0, [{'id': 'a', 'status': 'passed', 'reasons': []}])
            self.shard(root, 1, [{'id': 'b', 'status': 'profile_unsupported', 'reasons': expected['b']}])
            report = collector.collect(root, expected, 2, 'pin')
            self.assertTrue(report['complete'])
            self.assertTrue(report['passed'])
            (a / 'results.jsonl').write_text(json.dumps({'id': 'a', 'status': 'lean_unsupported', 'reasons': []}) + '\n')
            (a / 'summary.json').write_text(json.dumps({'lean_unsupported': 1}))
            report = collector.collect(root, expected, 2, 'pin')
            self.assertTrue(report['complete'])
            self.assertFalse(report['passed'])

    def test_missing_summary_duplicate_case_and_stale_sources_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            a = self.shard(root, 0, [{'id': 'a', 'status': 'passed', 'reasons': []}])
            b = self.shard(root, 1, [{'id': 'a', 'status': 'passed', 'reasons': []}])
            report = collector.collect(root, {'a': [], 'b': []}, 2, 'pin')
            self.assertFalse(report['complete'])
            self.assertEqual(report['duplicates'], ['a'])
            self.assertEqual(report['missing'], ['b'])
            (b / 'summary.json').unlink()
            report = collector.collect(root, {'a': []}, 2, 'other pin')
            self.assertFalse(report['complete'])
            self.assertFalse(report['passed'])
            self.assertTrue(any('source identity' in e for e in report['errors']))
            self.assertTrue(any('incomplete/invalid' in e for e in report['errors']))

    def test_only_excluded_profiles_can_have_unsupported_disposition(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.shard(root, 0, [{'id': 'a', 'status': 'profile_unsupported', 'reasons': []}])
            self.shard(root, 1, [{'id': 'b', 'status': 'passed', 'reasons': []}])
            self.assertFalse(collector.collect(root, {'a': [], 'b': []}, 2, 'pin')['passed'])

    def test_expected_ub_export_exit_requires_the_full_reference_oracle(self):
        # Fake tools exercise admission/failure propagation, not MIR semantics.
        case = next(c for c in discover() if c.id == 'fail/validity/invalid_bool.rs')
        line = case.errors[0][0]
        config = runtime_profile([]) | {'same_tcx': True}
        hash_value = 0xcbf29ce484222325
        for byte in b'{}':
            hash_value = ((hash_value ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
        sidecar = {'snapshot_byte_length': 2, 'snapshot_fnv1a64': f'{hash_value:016x}',
                   **{name + '_commit': (ROOT / f'upstream/.pins/{name}.commit').read_text().strip()
                      for name in ('miri', 'rustc')},
                   'reference': {'status': 'failed', 'config': config,
                                 'outcome': {'kind': 'miri_evaluation_error'}}}
        terminal = {'kind': 'ub', 'detail': 'invalidBool 2', 'frames': [
            {'file': case.path, 'line': line, 'end_line': line}]}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            native = root / 'runner'
            native.write_text('#!/usr/bin/env python3\nimport sys, json\n' +
                              'if sys.argv[1] == "--fingerprint":\n    print(' +
                              repr('upstream_fingerprint: ' + json.dumps({'byte_length': 2, 'fnv1a64': hash_value})) +
                              ')\nelse:\n    print(' + repr('upstream_result: ' + json.dumps(terminal)) + ')\n')
            native.chmod(0o700)
            for code, diagnostic, expected in (
                (2, f'error: Undefined Behavior: expected a boolean\n --> {case.path}:{line}:1', 'passed'),
                (1, f'error: Undefined Behavior: expected a boolean\n --> {case.path}:{line}:1', 'export_failed'),
                (2, 'error: unrelated compiler failure', 'reference_mismatch'),
            ):
                exporter = root / f'exporter-{code}-{len(diagnostic)}'
                exporter.write_text('''#!/usr/bin/env python3
import json, pathlib, sys
out = pathlib.Path(sys.argv[sys.argv.index('--output') + 1])
out.write_text('{}')
pathlib.Path(str(out) + '.miri-reference.json').write_text(json.dumps(SIDECAR))
print(DIAGNOSTIC)
sys.exit(CODE)
'''.replace('SIDECAR', repr(sidecar)).replace('DIAGNOSTIC', repr(diagnostic)).replace('CODE', str(code)))
                exporter.chmod(0o700)
                output = root / f'run-{code}-{len(diagnostic)}'
                output.mkdir()
                args = SimpleNamespace(exporter=exporter, runner=native, sysroot=root,
                                       export_timeout=10, timeout=10, keep_inputs=False)
                record = driver.run_case(case, args, __import__('os').environ.copy(), output)
                self.assertEqual(record['status'], expected)
                if expected != 'passed':
                    self.assertNotIn('lean_exit', record)


if __name__ == '__main__':
    unittest.main()
