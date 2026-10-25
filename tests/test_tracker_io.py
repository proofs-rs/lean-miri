import contextlib
import gzip
import hashlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import tracker_io, update_features


class TrackerIOTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def test_exact_bytes_deterministic_header_and_json(self):
        raw = b'{ "unicode": "\\u03bb", "rows": [2, 1] }\n'
        first, second = self.root/'first.json.gz', self.root/'second.json.gz'
        tracker_io.write_bytes(first, raw)
        tracker_io.write_bytes(second, raw)
        self.assertEqual(first.read_bytes(), second.read_bytes())
        self.assertEqual(first.read_bytes()[3:10], b'\x00\x00\x00\x00\x00\x02\xff')
        self.assertEqual(tracker_io.read_bytes(first), raw)
        self.assertEqual(hashlib.sha256(gzip.decompress(first.read_bytes())).digest(), hashlib.sha256(raw).digest())
        self.assertEqual(tracker_io.read_json(first), {'unicode': 'λ', 'rows': [2, 1]})

    def test_plain_json_compatibility_and_canonical_encoding(self):
        data = {'z': 'λ', 'a': [1, 2]}
        plain, compressed = self.root/'data.json', self.root/'data.json.gz'
        tracker_io.write_json(plain, data)
        tracker_io.write_json(compressed, data)
        self.assertEqual(plain.read_bytes(), tracker_io.read_bytes(compressed))
        self.assertEqual(tracker_io.read_json(plain), data)

    def test_corruption_truncation_and_trailing_junk_rejected(self):
        path = self.root/'data.json.gz'
        tracker_io.write_json(path, {'value': [1, 2, 3]})
        valid = path.read_bytes()
        corrupted = bytearray(valid)
        corrupted[-8] ^= 1  # CRC32
        for raw in [valid[:-1], valid[:10], bytes(corrupted), valid + b'junk', b'not gzip']:
            with self.subTest(raw=raw):
                path.write_bytes(raw)
                with self.assertRaises(tracker_io.TrackerIOError):
                    tracker_io.read_json(path)

    def test_invalid_json_and_utf8_rejected(self):
        path = self.root/'data.json.gz'
        for raw in [b'{', b'\xff']:
            tracker_io.write_bytes(path, raw)
            with self.assertRaises(tracker_io.TrackerIOError):
                tracker_io.read_json(path)

    def test_failed_atomic_replace_preserves_previous_file(self):
        path = self.root/'data.json.gz'
        tracker_io.write_json(path, {'old': True})
        before = path.read_bytes()
        with patch('tools.tracker_io.os.replace', side_effect=OSError('replacement failed')):
            with self.assertRaises(tracker_io.TrackerIOError):
                tracker_io.write_json(path, {'new': True})
        self.assertEqual(path.read_bytes(), before)
        self.assertEqual(list(self.root.iterdir()), [path])

    def test_dependency_cli_stale_corrupt_and_missing_fail_closed(self):
        features = self.root/'tracking/features.json'
        tracker_io.write_json(features, {'schema_version': 1, 'features': []})
        dependency_path = self.root/'tracking/dependencies.json.gz'
        generated = {'schema_version': 1, 'dependencies': [], 'scope': 'current'}
        patches = [patch.object(update_features, 'load_inventory', return_value={'symbols': []}),
                   patch.object(update_features, 'validate_inventory', return_value={}),
                   patch.object(update_features, 'build_ast_features', return_value=[]),
                   patch.object(update_features, 'build_dependency_inventory', return_value=generated)]
        with contextlib.ExitStack() as stack:
            for mocked in patches:
                stack.enter_context(mocked)
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
            self.assertEqual(update_features.main(['--root', str(self.root), '--check']), 1)
            tracker_io.write_json(dependency_path, {**generated, 'scope': 'stale'})
            self.assertEqual(update_features.main(['--root', str(self.root), '--check']), 1)
            self.assertEqual(update_features.main(['--root', str(self.root), '--write']), 0)
            self.assertEqual(update_features.main(['--root', str(self.root), '--check']), 0)
            self.assertEqual(tracker_io.read_json(dependency_path), generated)
            dependency_path.write_bytes(dependency_path.read_bytes()[:-1])
            self.assertEqual(update_features.main(['--root', str(self.root), '--check']), 2)


if __name__ == '__main__':
    unittest.main()
