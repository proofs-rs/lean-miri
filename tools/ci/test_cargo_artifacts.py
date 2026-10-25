import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    'cargo_artifacts', Path(__file__).resolve().parents[1] / 'cargo_artifacts.py')
artifacts = importlib.util.module_from_spec(spec)
spec.loader.exec_module(artifacts)


def artifact(name, paths):
    return json.dumps({'reason': 'compiler-artifact',
                       'target': {'name': name, 'kind': ['lib']},
                       'filenames': [str(p) for p in paths]})


class CargoArtifactTests(unittest.TestCase):
    def test_selects_emitted_archive_without_filename_or_directory_guess(self):
        with tempfile.TemporaryDirectory() as tmp:
            archive = Path(tmp) / 'different layout' / 'actual-library.rlib'
            archive.parent.mkdir()
            archive.touch()
            messages = '\n'.join([
                json.dumps({'reason': 'build-script-executed'}),
                artifact('other', [Path(tmp) / 'unrelated.rlib']),
                artifact('libc', [archive.with_suffix('.rmeta'), archive]),
                artifact('libc', [archive]),
            ])
            self.assertEqual(artifacts.select_rlib(messages, 'libc'), archive.resolve())

    def test_ambiguous_archives_fail(self):
        with self.assertRaisesRegex(ValueError, 'got 2'):
            artifacts.select_rlib(artifact('libc', ['/tmp/a.rlib', '/tmp/b.rlib']), 'libc')

    def test_missing_archive_fails(self):
        with self.assertRaisesRegex(ValueError, 'got 0'):
            artifacts.select_rlib(artifact('libc', ['/tmp/a.rmeta']), 'libc')

    def test_nonexistent_reported_archive_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(ValueError, 'does not exist'):
                artifacts.select_rlib(artifact('libc', [Path(tmp) / 'absent.rlib']), 'libc')

    def test_malformed_cargo_message_fails(self):
        with self.assertRaises(json.JSONDecodeError):
            artifacts.select_rlib('not JSON', 'libc')


if __name__ == '__main__':
    unittest.main()
