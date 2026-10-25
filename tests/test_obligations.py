import importlib.util
from pathlib import Path
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "extract_obligations", Path(__file__).resolve().parents[1] / "tools/extract_obligations.py")
scanner = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(scanner)


class ObligationCandidates(unittest.TestCase):
    def test_categories_and_source_identity(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "source.rs"
            source.write_text('throw_ub_format!("bad");\nrng.random_range(0..3);\n'
                              'TerminatorKind::Call { .. }\nuse rustc_abi::Size;\n')
            found = scanner.scan_file(source, "source.rs")
            self.assertEqual([x["category"] for x in found],
                             ["ub", "nondeterministic_choice", "mir_dispatch", "external_dependency"])
            self.assertEqual([x["line"] for x in found], [1, 2, 3, 4])
            previous = found[0]["source_sha256"]
            source.write_text('throw_ub_format!("changed");\n')
            self.assertNotEqual(scanner.scan_file(source, "source.rs")[0]["source_sha256"], previous)

    def test_missing_source_is_failure(self):
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaises(ValueError):
                scanner.collect(Path(temporary))

    def test_comments_remain_explicit_review_candidates(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "source.rs"
            source.write_text('// throw_ub_format! is mentioned in documentation\n')
            found = scanner.scan_file(source, "source.rs")
            self.assertEqual(found[0]["review"], "pending")
            self.assertEqual(found[0]["category"], "ub")


if __name__ == "__main__":
    unittest.main()
