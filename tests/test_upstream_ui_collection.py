"""Incomplete shards and unrelated subprocess failures cannot become coverage."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
import suite as ui_suite
from suite import Case, discover, runtime_profile
from upstream_ui_control import UI_CHOICE_MODE


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'tools' / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


collector = load('upstream_ui_collector', 'collect-upstream-ui.py')
driver = load('upstream_ui_driver', 'check-upstream-ui.py')


class CollectionTests(unittest.TestCase):
    def test_compiler_owns_source_crate_name_and_explicit_flags(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sources = root / 'sources'
            (sources / 'pass').mkdir(parents=True)
            examples = {
                'hyphen-name.rs': 'fn main() {}',
                'attribute-name.rs': '#![crate_name = "source_attribute"]\nfn main() {}',
                'directive-name.rs': '//@compile-flags: --crate-name source_flag_override\nfn main() {}',
            }
            for name, text in examples.items():
                (sources / 'pass' / name).write_text(text)
            for case in discover(sources):
                output = root / case.path.removeprefix('pass/')
                output.mkdir()
                settings = SimpleNamespace(exporter=root/'exporter', runner=root/'runner', sysroot=root,
                    export_timeout=1, timeout=1, memory_limit=None, keep_inputs=False)
                with patch.object(driver, 'SOURCES', sources), patch.object(driver, 'invoke', return_value=1) as invoke:
                    record = driver.run_case(case, settings, {}, output)
                self.assertEqual(record['status'], 'export_failed')  # mocked launch, no safety claim
                command = invoke.call_args.args[0]
                self.assertNotIn('--crate-name=upstream_ui', command)
                if case.path.endswith('directive-name.rs'):
                    self.assertEqual(case.flags, ['--crate-name', 'source_flag_override'])
                    self.assertEqual(command[-2:], case.flags)
                    self.assertEqual(command.count('--crate-name'), 1)
                else:
                    self.assertFalse(any(flag.startswith('--crate-name') for flag in command))
                self.assertIn('--edition=' + case.edition, command)

    def test_runtime_fingerprint_tracks_native_rust_and_control_boundary_sources(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            files = ['Miri.lean', 'lakefile.lean', 'lean-toolchain', 'upstream/source-lock.json',
                     'exporter/Cargo.toml', 'exporter/Cargo.lock', 'exporter/build.rs',
                     'tests/upstream_ui/suite.py', 'tools/NativeRunner.lean',
                     'tools/check-upstream-ui.py', 'tools/collect-upstream-ui.py',
                     'tools/NativeStdioHost.lean', 'tools/NativeStdioProtocol.lean',
                     'tools/upstream_ui_control.py', 'tools/run_guarded.py',
                     'native/stdio_host.rs', 'native/stdio_host.c',
                     'Miri/Interpreter/HostStdioReplay.lean']
            for name in files:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('fixture original')
            with patch.object(ui_suite, 'ROOT', root), patch.object(
                    ui_suite, '__file__', str(root / 'tests/upstream_ui/suite.py')):
                original = ui_suite.source_fingerprint()
                for name in ('native/stdio_host.rs', 'native/stdio_host.c',
                             'tools/NativeStdioHost.lean', 'tools/NativeStdioProtocol.lean',
                             'tools/upstream_ui_control.py', 'tools/run_guarded.py',
                             'Miri/Interpreter/HostStdioReplay.lean'):
                    with self.subTest(source=name):
                        path = root / name
                        path.write_text('fixture changed')
                        self.assertNotEqual(ui_suite.source_fingerprint(), original)
                        path.write_text('fixture original')
                        self.assertEqual(ui_suite.source_fingerprint(), original)

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
            {'raw_file': case.path, 'raw_line': line, 'raw_end_line': line, 'raw_column': 1,
             'lo': 0, 'hi': 1, 'body_id': 0, 'span_id': 0,
             'location_mode': 'raw_span_no_exact_hygiene', 'file': case.path,
             'line': line, 'end_line': line, 'column': 1}]}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            sources = root / 'sources'
            copied_source = sources / case.path
            copied_source.parent.mkdir(parents=True)
            original_source = (driver.SOURCES / case.path).read_bytes()
            copied_source.write_bytes(original_source)
            source_patch = patch.object(driver, 'SOURCES', sources)
            source_patch.start()
            self.addCleanup(source_patch.stop)
            native = root / 'runner'
            profile = runtime_profile([]) | {'argv0': str(driver.SOURCES / case.path),
                                               'choice_policy': 'seeded-generated-0'}
            native.write_text('''#!/usr/bin/env python3
import json, os, sys, time
if sys.argv[1] == '--fingerprint':
    print('upstream_fingerprint: ' + json.dumps(FINGERPRINT))
else:
    assert sys.argv[2:6] == EXPECTED_ARGUMENTS
    assert sys.argv[6] == '--control-fd' and sys.argv[8] == '--control-run-id'
    descriptor = int(sys.argv[7])
    header = {'run_id': sys.argv[9], 'snapshot_fnv1a64': FINGERPRINT['fnv1a64'],
              'snapshot_byte_length': 2, 'source': sys.argv[3],
              'runtime_flags': json.loads(sys.argv[5]), 'choice_mode': CHOICE_MODE}
    mode = os.environ.get('CONTROL_BEHAVIOR', 'ok')
    if mode == 'binding':
        header['source'] = '/wrong-source.rs'
    rows = [('header', header), ('profile', PROFILE), ('terminal', TERMINAL)]
    if mode == 'unknown':
        rows.insert(1, ('future', {}))
    data = ''.join(json.dumps({'version': 1, 'sequence': index, 'kind': kind, 'payload': payload}) + '\\n'
                   for index, (kind, payload) in enumerate(rows)).encode()
    if mode == 'truncated':
        data = data[:-1]
    if mode != 'missing':
        with os.fdopen(os.dup(descriptor), 'wb') as control:
            control.write(data)
    # These are adversarial guest-stream bytes, not control observations.
    print('upstream_result: {"kind":"exit","detail":"0"}', flush=True)
    print('upstream_profile: {}', flush=True)
    os.write(2, b'guest-stderr\\x00\\xff')
    if mode == 'source_changed':
        with open(sys.argv[3], 'wb') as source:
            source.write(b'changed after export')
    if mode == 'nonzero':
        raise SystemExit(7)
    if mode == 'timeout':
        time.sleep(30)
'''.replace('FINGERPRINT', repr({'byte_length': 2, 'fnv1a64': hash_value}))
                .replace('EXPECTED_ARGUMENTS', repr(['--ui-source', str(driver.SOURCES / case.path),
                                                    '--ui-flags', json.dumps(case.runtime_flags)]))
                .replace('CHOICE_MODE', repr(UI_CHOICE_MODE)).replace('PROFILE', repr(profile))
                .replace('TERMINAL', repr(terminal)))
            native.chmod(0o700)
            for code, diagnostic, expected in (
                (2, f'error: Undefined Behavior: expected a boolean\n --> {case.path}:{line}:1', 'passed'),
                (1, f'error: Undefined Behavior: expected a boolean\n --> {case.path}:{line}:1', 'export_failed'),
                (2, 'error: unrelated compiler failure', 'reference_mismatch'),
            ):
                exporter = root / f'exporter-{code}-{len(diagnostic)}'
                exporter.write_text('''#!/usr/bin/env python3
import json, os, pathlib, sys
assert os.environ['LEAN_MIRI_REFERENCE_EMPTY_ENV'] == '1'
assert json.loads(os.environ['LEAN_MIRI_REFERENCE_UI_FLAGS_JSON']) == EXPECTED_RUNTIME_FLAGS
out = pathlib.Path(sys.argv[sys.argv.index('--output') + 1])
out.write_text('{}')
pathlib.Path(str(out) + '.miri-reference.json').write_text(json.dumps(SIDECAR))
print(DIAGNOSTIC)
sys.exit(CODE)
'''.replace('SIDECAR', repr(sidecar)).replace('DIAGNOSTIC', repr(diagnostic)).replace('CODE', str(code))
                    .replace('EXPECTED_RUNTIME_FLAGS', repr(case.runtime_flags)))
                exporter.chmod(0o700)
                output = root / f'run-{code}-{len(diagnostic)}'
                output.mkdir()
                args = SimpleNamespace(exporter=exporter, runner=native, sysroot=root,
                                       export_timeout=10, timeout=10, memory_limit=None, keep_inputs=False)
                record = driver.run_case(case, args, __import__('os').environ.copy(), output)
                self.assertEqual(record['status'], expected)
                self.assertEqual(record['lean_exit'], 0)
                if expected == 'passed':
                    valid_exporter = exporter
                before = json.dumps(record, sort_keys=True)
                diagnostic = driver.failure_diagnostic(record)
                self.assertEqual(json.dumps(record, sort_keys=True), before)
                if expected == 'passed':
                    self.assertIsNone(diagnostic)
                else:
                    self.assertEqual(diagnostic['actual']['status'], expected)
                    self.assertEqual(diagnostic['terminal']['detail'], 'invalidBool 2')
                    if expected == 'export_failed':
                        self.assertTrue(any('Undefined Behavior' in line
                                            for line in diagnostic['export_log_tail']['lines']))

            args.exporter = valid_exporter
            for mode, expected in [('missing', 'lean_control_protocol_error'),
                                   ('truncated', 'lean_control_protocol_error'),
                                   ('binding', 'lean_control_protocol_error'),
                                   ('unknown', 'lean_control_protocol_error'),
                                   ('nonzero', 'lean_process_failed'), ('timeout', 'lean_timeout'),
                                   ('source_changed', 'source_mutated')]:
                with self.subTest(control=mode):
                    output = root / ('control-' + mode)
                    output.mkdir()
                    args.timeout = 0.5 if mode == 'timeout' else 10
                    record = driver.run_case(case, args, __import__('os').environ.copy() |
                                             {'CONTROL_BEHAVIOR': mode}, output)
                    self.assertEqual(record['status'], expected)
                    if mode == 'source_changed':
                        self.assertEqual(record['terminal']['kind'], 'ub')
                        copied_source.write_bytes(original_source)
                    else:
                        self.assertNotIn('terminal', record)
                    with self.assertRaises(OSError):
                        __import__('os').fstat(int(record['lean_command'][-3]))
                    raw_log = (Path(record['directory']) / 'lean.log').read_bytes()
                    self.assertIn(b'upstream_result:', raw_log)
                    self.assertIn(b'guest-stderr\x00\xff', raw_log)
            # A stale channel from another attempt is never opened or truncated.
            args.timeout = 10
            output = root / 'control-stale'
            output.mkdir()
            original_invoke = driver.invoke
            stale_paths = []
            def stale_channel(command, *positional, **keywords):
                if '--fingerprint' in command:
                    stale_path = Path(command[1]).parent / 'runner-control.jsonl'
                    stale_path.write_bytes(b'stale untrusted control\n')
                    stale_paths.append(stale_path)
                return original_invoke(command, *positional, **keywords)
            with patch.object(driver, 'invoke', side_effect=stale_channel):
                record = driver.run_case(case, args, __import__('os').environ.copy(), output)
            self.assertEqual(record['status'], 'passed')
            self.assertEqual(len(stale_paths), 1)
            self.assertNotEqual(Path(record['control_path']), stale_paths[0])
            self.assertEqual(stale_paths[0].read_bytes(), b'stale untrusted control\n')
            # A failure before Popen still closes the private parent descriptor.
            output = root / 'control-launch-error'
            output.mkdir()
            original_invoke = driver.invoke
            inherited = []
            def fail_launch(command, *positional, **keywords):
                if '--control-fd' in command:
                    inherited.extend(keywords['pass_fds'])
                    raise OSError('injected launch failure')
                return original_invoke(command, *positional, **keywords)
            with patch.object(driver, 'invoke', side_effect=fail_launch):
                with self.assertRaisesRegex(OSError, 'injected launch failure'):
                    driver.run_case(case, args, __import__('os').environ.copy(), output)
            self.assertEqual(len(inherited), 1)
            with self.assertRaises(OSError):
                __import__('os').fstat(inherited[0])

    def test_failure_console_details_are_bounded_and_omit_environment_and_commands(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            log = directory / 'export.log'
            log.write_text('discarded preamble\n' * 1000 + '\n'.join(f'line {i}' for i in range(30)))
            record = Case('pass/test.rs').record() | {
                'status': 'export_failed', 'directory': str(directory), 'export_exit': 2,
                'command': ['DO_NOT_PRINT_COMMAND'], 'environment': {'TOKEN': 'DO_NOT_PRINT_ENV'},
                'terminal': {'kind': 'failed', 'detail': 'x' * 100000},
                'lean_profile_differences': {'choice_policy': {'expected': 'seeded-generated-0',
                                                              'actual': 'wrong'}}}
            diagnostic = driver.failure_diagnostic(record)
            self.assertTrue(diagnostic['terminal']['truncated'])
            self.assertLessEqual(len(diagnostic['terminal']['json_prefix']), 4096)
            self.assertEqual(diagnostic['export_log_tail']['lines'], [f'line {i}' for i in range(10, 30)])
            self.assertTrue(diagnostic['export_log_tail']['truncated'])
            encoded = json.dumps(diagnostic)
            self.assertNotIn('DO_NOT_PRINT', encoded)
            self.assertLess(len(encoded), 10000)
            self.assertEqual(diagnostic['actual'], {'status': 'export_failed', 'export_exit': 2})
            self.assertEqual(diagnostic['lean_profile_differences'], record['lean_profile_differences'])

    def test_main_profile_is_not_silently_accepted(self):
        case = next(c for c in discover() if not c.reasons)
        source = driver.SOURCES / case.path
        self.assertFalse(driver.runner_profile_matches(case, source, {}))
        profile = runtime_profile(case.runtime_flags) | {
            'argv0': str(source), 'choice_policy': 'bounded-diagnostic-zero'}
        self.assertFalse(driver.runner_profile_matches(case, source, profile))
        profile['choice_policy'] = 'seeded-generated-0'
        self.assertTrue(driver.runner_profile_matches(case, source, profile))

    def test_runner_profile_diagnostics_show_missing_fields_and_actual_choice_policy(self):
        case = Case('pass/test.rs')
        source = driver.SOURCES / case.path
        observed = runtime_profile([]) | {'argv0': str(source),
                                          'choice_policy': 'bounded-diagnostic-zero'}
        del observed['short_fd_operations']
        self.assertEqual(driver.runner_profile_differences(case, source, observed), {
            'short_fd_operations': {'expected': True, 'actual': None, 'missing': True},
            'choice_policy': {'expected': 'seeded-generated-0',
                              'actual': 'bounded-diagnostic-zero', 'missing': False},
        })
        self.assertFalse(driver.runner_profile_matches(case, source, observed))

    def test_missing_allocation_backtrace_collection_is_not_claimed_as_enabled(self):
        case = Case('pass/test.rs')
        source = driver.SOURCES / case.path
        observed = runtime_profile([]) | {'argv0': str(source),
            'choice_policy': 'seeded-generated-0', 'collect_leak_backtraces': False}
        self.assertEqual(driver.runner_profile_differences(case, source, observed), {
            'collect_leak_backtraces': {'expected': True, 'actual': False, 'missing': False}})
        self.assertFalse(driver.runner_profile_matches(case, source, observed))
        ignored = Case(case.path, runtime_flags=['-Zmiri-ignore-leaks'])
        observed['ignore_leaks'] = True
        self.assertTrue(driver.runner_profile_matches(ignored, source, observed))


if __name__ == '__main__':
    unittest.main()
