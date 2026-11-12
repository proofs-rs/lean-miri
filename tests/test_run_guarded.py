"""Optional host guards never turn a killed child into successful execution."""
import pathlib
import os
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

    def test_only_explicit_pass_fds_are_inherited_and_parent_retains_ownership(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            kept = os.open(root / 'kept', os.O_CREAT | os.O_RDWR, 0o600)
            hidden = os.open(root / 'hidden', os.O_CREAT | os.O_RDWR, 0o600)
            try:
                os.set_inheritable(hidden, True)
                script = (f'import os; os.write({kept}, b"control"); '
                          f'\ntry: os.fstat({hidden})'
                          '\nexcept OSError: pass'
                          '\nelse: raise SystemExit("unrelated FD leaked")')
                result = run([sys.executable, '-c', script], cwd=root, env=None,
                             log=root / 'run.log', timeout=5, memory_limit=None,
                             pass_fds=(kept,))
                self.assertEqual(result.returncode, 0)
                self.assertFalse(os.get_inheritable(kept))
                os.lseek(kept, 0, os.SEEK_SET)
                self.assertEqual(os.read(kept, 100), b'control')
                os.fstat(kept)
            finally:
                os.close(kept)
                os.close(hidden)

    def test_default_does_not_inherit_even_an_inheritable_fd(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = pathlib.Path(temporary)
            descriptor = os.open(root / 'private', os.O_CREAT | os.O_RDWR, 0o600)
            try:
                os.set_inheritable(descriptor, True)
                script = (f'import os\ntry: os.fstat({descriptor})'
                          '\nexcept OSError: pass'
                          '\nelse: raise SystemExit("default FD leaked")')
                result = run([sys.executable, '-c', script], cwd=root, env=None,
                             log=root / 'run.log', timeout=5, memory_limit=None)
                self.assertEqual(result.returncode, 0)
                os.fstat(descriptor)
            finally:
                os.close(descriptor)


if __name__ == '__main__':
    unittest.main()
