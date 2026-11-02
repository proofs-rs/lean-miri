"""Storage checks for immutable DAG reuse; no Lean execution is needed."""
import errno
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / 'tools/check-duplicate-prefix-dag.py'
SPEC = importlib.util.spec_from_file_location('duplicate_prefix_dag', SCRIPT)
dag = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(dag)


class ArtifactStorage(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.origin = self.root / 'cached.olean'
        self.origin.write_bytes(b'kernel checked immutable artifact')
        self.target = self.root / 'reused.olean'
        self.expected = dag.digest(self.origin)

    def test_link_and_fresh_output_have_separate_lifetimes(self):
        dag.install_artifact(self.origin, self.target, self.expected, link=True)
        self.assertEqual(self.origin.stat().st_ino, self.target.stat().st_ino)
        self.assertEqual(dag.digest(self.target), self.expected)
        fresh = self.root / 'fresh.olean'
        dag.require_fresh_target(fresh)
        fresh.write_bytes(b'new independently compiled output')
        self.assertNotEqual(fresh.stat().st_ino, self.origin.stat().st_ino)
        self.assertEqual(dag.digest(self.origin), self.expected)

    def test_default_copies(self):
        dag.install_artifact(self.origin, self.target, self.expected)
        self.assertNotEqual(self.origin.stat().st_ino, self.target.stat().st_ino)
        self.assertEqual(dag.digest(self.target), self.expected)

    def test_existing_target_cannot_be_overwritten(self):
        self.target.write_bytes(b'preserve existing output')
        for link in (False, True):
            with self.assertRaises(FileExistsError):
                dag.install_artifact(self.origin, self.target, self.expected, link=link)
        with self.assertRaises(FileExistsError):
            dag.require_fresh_target(self.target)
        self.assertEqual(self.target.read_bytes(), b'preserve existing output')

    def test_hash_mismatch_never_installs(self):
        with self.assertRaises(RuntimeError):
            dag.install_artifact(self.origin, self.target, 'wrong', link=True)
        self.assertFalse(self.target.exists())

    def test_exdev_copies_but_other_link_errors_fail(self):
        with patch.object(dag.os, 'link', side_effect=OSError(errno.EXDEV, 'cross-device')):
            dag.install_artifact(self.origin, self.target, self.expected, link=True)
        self.assertNotEqual(self.origin.stat().st_ino, self.target.stat().st_ino)
        other = self.root / 'other.olean'
        with patch.object(dag.os, 'link', side_effect=OSError(errno.EPERM, 'denied')):
            with self.assertRaises(OSError):
                dag.install_artifact(self.origin, other, self.expected, link=True)
        self.assertFalse(other.exists())

    def test_failed_output_without_manifest_is_ineligible(self):
        with self.assertRaises(FileNotFoundError):
            dag.load_reuse(self.root)

    def test_mode_is_explicit_and_default_is_copy(self):
        self.assertFalse(dag.parser().parse_args([]).link_reused_artifacts)
        self.assertTrue(dag.parser().parse_args(['--reuse', str(self.root),
                                               '--link-reused-artifacts']).link_reused_artifacts)


if __name__ == '__main__':
    unittest.main()
