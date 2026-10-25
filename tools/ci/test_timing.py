import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from time_command import measure, read_steps


class TimingTests(unittest.TestCase):
    def test_records_failure_arguments_and_resource_usage(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'steps.jsonl'
            command = [sys.executable, '-c', 'import sys; sys.exit(int(sys.argv[1]))', '7']
            self.assertEqual(measure('comparison:negative', command, path), 7)
            rows, errors = read_steps(path)
            self.assertEqual(errors, [])
            self.assertEqual(len(rows), 1)
            row = rows[0]
            self.assertEqual(row['command'], command)
            self.assertEqual(row['status'], 'failed')
            self.assertEqual(row['exit_code'], 7)
            self.assertGreater(row['seconds'], 0)
            self.assertGreaterEqual(row['user_seconds'], 0)
            self.assertGreater(row['max_child_rss_kib'], 0)

    def test_interrupted_step_is_not_reported_as_passed(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'steps.jsonl'
            path.write_text(json.dumps(dict(id='one', event='start', label='build:x')) + '\n')
            rows, errors = read_steps(path)
            self.assertEqual(errors, [])
            self.assertEqual(rows[0]['status'], 'interrupted')
            self.assertNotIn('seconds', rows[0])

    def test_truncated_event_does_not_hide_completed_steps(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'steps.jsonl'
            measure('assertions:ok', [sys.executable, '-c', 'pass'], path)
            with path.open('a') as stream:
                stream.write('{"id":')
            rows, errors = read_steps(path)
            self.assertEqual(rows[0]['status'], 'passed')
            self.assertEqual(len(errors), 1)

    def test_shell_wrapper_preserves_arguments_environment_and_failure(self):
        helper = Path(__file__).with_name('timing.sh').resolve()
        script = 'source "$1"; ci_step comparison:args bash -c '\
                 '\'[[ "$MARKER" == "two words" && "$1" == "a b" ]] || exit 9; exit 7\' -- "a b"'
        with tempfile.TemporaryDirectory() as tmp:
            for enabled in [False, True]:
                path = Path(tmp) / 'steps.jsonl'
                env = dict(os.environ, MARKER='two words')
                env.pop('CI_TIMING_FILE', None)
                if enabled:
                    env['CI_TIMING_FILE'] = str(path)
                result = subprocess.run(['bash', '-c', script, '--', str(helper)], env=env,
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertEqual(path.exists(), enabled)
                if enabled:
                    self.assertEqual(read_steps(path)[0][0]['exit_code'], 7)

    def test_shell_wrapper_keeps_fail_fast_behavior(self):
        helper = Path(__file__).with_name('timing.sh').resolve()
        script = 'set -e; source "$1"; ci_step assertions:failure bash -c "exit 7"; touch "$2"'
        with tempfile.TemporaryDirectory() as tmp:
            sentinel = Path(tmp) / 'should-not-exist'
            for enabled in [False, True]:
                env = os.environ.copy()
                env.pop('CI_TIMING_FILE', None)
                if enabled:
                    env['CI_TIMING_FILE'] = str(Path(tmp) / 'steps.jsonl')
                result = subprocess.run(['bash', '-c', script, '--', str(helper), str(sentinel)],
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 7, result.stderr)
                self.assertFalse(sentinel.exists())


if __name__ == '__main__':
    unittest.main()
