"""Collector launch/classification checks; the fake runner tests no MIR semantics."""
import json
import importlib.util
from unittest import mock
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
COLLECTOR = ROOT / 'tools/measure.py'


class MeasureTests(unittest.TestCase):
    def test_default_build_freezes_binary_and_reports_failure(self):
        spec = importlib.util.spec_from_file_location('measure', COLLECTOR)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            binary = root / '.lake/build/bin/native_runner'
            binary.parent.mkdir(parents=True)
            binary.write_bytes(b'first executable')
            output = root / 'out'
            output.mkdir()
            with mock.patch.object(module, 'ROOT', root), mock.patch.object(module.subprocess, 'run') as build:
                build.return_value.returncode = 0
                frozen, log = module.build_native_snapshot(output, {})
                self.assertEqual(build.call_args.args[0], [str(root / '.elan/bin/lake'), 'build', 'native_runner'])
                self.assertTrue(log.exists())
                binary.write_bytes(b'replaced executable')
                self.assertEqual(frozen.read_bytes(), b'first executable')
                build.return_value.returncode = 1
                with self.assertRaisesRegex(SystemExit, 'build failed; log:'):
                    module.build_native_snapshot(output, {})
                self.assertEqual(len(list(output.glob('native-artifacts-*'))), 1)

    def test_native_launch_without_lean_path(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            runner = root / 'runner'
            runner.write_text("#!/bin/sh\nprintf '%s\\n' 'decode: ready obligations=0' 'candidate=0: finalized_exit code=42' 'run: finalized_exit code=42'\n")
            runner.chmod(0o700)
            inp = root / 'input.json'
            inp.write_text('{}')
            # Follow the test process affinity; do not assume CPU2 is available.
            cpu = min(os.sched_getaffinity(0))
            env = os.environ.copy()
            env.pop('LEAN_PATH', None)
            result = subprocess.run([sys.executable, str(COLLECTOR), '--input', str(inp),
                '--name', 'native', '--executable', str(runner), '--runs', '1',
                '--cpu', str(cpu), '--timeout', '10', '--output-dir', str(root / 'out')],
                env=env, capture_output=True, text=True, timeout=20)
            self.assertEqual(result.returncode, 0, result.stderr)
            summary = json.loads((root / 'out/native-summary.json').read_text())
            self.assertEqual(summary['execution_mode'], 'native')
            self.assertIsNone(summary['lean_path'])
            self.assertNotIn('--run', summary['command'])
            self.assertEqual(summary['command'][-2:], [str(runner), str(inp)])
            self.assertTrue(summary['runs'][0]['finalized_exit_observed'])
            seeded = subprocess.run([sys.executable, str(COLLECTOR), '--input', str(inp),
                '--name', 'seeded', '--executable', str(runner), '--runs', '1',
                '--cpu', str(cpu), '--seed', '0', '--profile', '--output-dir', str(root / 'out')],
                env=env, capture_output=True, text=True, timeout=20)
            self.assertEqual(seeded.returncode, 0, seeded.stderr)
            seeded_summary = json.loads((root / 'out/seeded-summary.json').read_text())
            self.assertEqual(seeded_summary['command'][-3:], ['--seed', '0', '--profile'])
            self.assertEqual(seeded_summary['diagnostic_seed'], 0)
            self.assertTrue(seeded_summary['profile_requested'])
            self.assertEqual(seeded_summary['collector_version'], 'runner-7')


    def test_seed_outside_u64_is_rejected_before_launch(self):
        for seed in ['-1', str(2**64)]:
            result = subprocess.run([sys.executable, str(COLLECTOR), '--input', 'unused',
                '--name', 'unused', '--seed', seed, '--executable', 'unused'],
                capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn('unsigned u64', result.stderr)

    def test_runner_and_executable_are_mutually_exclusive(self):
        result = subprocess.run([sys.executable, str(COLLECTOR), '--input', 'unused',
            '--name', 'unused', '--runner', 'unused', '--executable', 'unused'],
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('not allowed with argument', result.stderr)


if __name__ == '__main__':
    unittest.main()
