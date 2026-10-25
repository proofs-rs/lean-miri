"""Exercise CI failure/timeout propagation without toolchain downloads."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('ci_run', Path(__file__).with_name('run.py'))
ci = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = ci
spec.loader.exec_module(ci)


class RunnerTests(unittest.TestCase):
    def test_continues_after_failure_and_records_commands_and_logs(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            selected = [ci.Suite('bad', (sys.executable, '-c', 'raise SystemExit(7)')),
                        ci.Suite('good', (sys.executable, '-c', 'print("reached")'))]
            with patch.dict('os.environ', {'GITHUB_STEP_SUMMARY': str(output / 'github.md')}):
                self.assertEqual(ci.run_all(selected, output, {'commit': 'test'}), 1)
            report = json.loads((output / 'results.json').read_text())
            self.assertTrue(report['complete'])
            self.assertEqual([r['status'] for r in report['results']], ['failed', 'passed'])
            self.assertEqual(report['results'][0]['exit_code'], 7)
            self.assertEqual(report['results'][1]['command'], list(selected[1].command))
            self.assertIn('reached', (output / 'good.log').read_text())
            self.assertIn('| bad | failed |', (output / 'github.md').read_text())

    def test_timeout_is_failure_and_next_suite_runs(self):
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            selected = [ci.Suite('slow', (sys.executable, '-c', 'import time; time.sleep(60)'), 0.05),
                        ci.Suite('after', (sys.executable, '-c', 'pass'))]
            self.assertEqual(ci.run_all(selected, output, {}), 1)
            rows = json.loads((output / 'results.json').read_text())['results']
            self.assertEqual([r['status'] for r in rows], ['timeout', 'passed'])

    def test_missing_command_is_failure(self):
        with tempfile.TemporaryDirectory() as temp:
            row = ci.execute(ci.Suite('missing', ('/nonexistent/lean-miri-ci-command',)), Path(temp))
            self.assertEqual(row['status'], 'failed')
            self.assertIsNone(row['exit_code'])

    def test_successful_lane_returns_zero(self):
        with tempfile.TemporaryDirectory() as temp:
            self.assertEqual(ci.run_all([ci.Suite('ok', (sys.executable, '-c', 'pass'))], Path(temp), {}), 0)


if __name__ == '__main__':
    unittest.main()
