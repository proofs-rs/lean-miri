"""Optional host guards never turn a killed child into successful execution."""
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
from run_guarded import run


class OptionalGuards(unittest.TestCase):
    def invoke(self, script, **guards):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            return run([sys.executable, '-c', script], cwd=root, env=None,
                       log=root / 'run.log', **guards)

    def test_unlimited_preserves_child_exit(self):
        result = self.invoke('raise SystemExit(7)', timeout=None, memory_limit=None)
        self.assertEqual(result.returncode, 7)

    def test_explicit_wall_guard_fails(self):
        with self.assertRaisesRegex(RuntimeError, 'walltime limit'):
            self.invoke('import time; time.sleep(30)', timeout=0.01, memory_limit=None)

    def test_explicit_memory_guard_remains_available(self):
        if not pathlib.Path('/sys/fs/cgroup/memory.current').exists():
            self.skipTest('no cgroup memory counter')
        with self.assertRaisesRegex(RuntimeError, 'NOT RUN'):
            self.invoke('pass', timeout=None, memory_limit=1)


if __name__ == '__main__':
    unittest.main()
