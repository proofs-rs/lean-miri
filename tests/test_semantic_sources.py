import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("semantic_sources", Path(__file__).resolve().parents[1] / "tools/check_semantic_sources.py")
lint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lint)


class SemanticSourceLint(unittest.TestCase):
    def test_default_fallbacks_are_rejected(self):
        text = 'def f := panic! "bad"\ndef g := values[i]!\ndef h := a.set! i x\n'
        self.assertEqual([line for line, _ in lint.violations(text)], [1, 2, 3])

    def test_nested_comments_and_strings_are_not_code(self):
        text = '/- panic! /- get! -/ unreachable! -/\n-- values[i]!\n"panic! \\" get!"\ndef f := Except.error 7\n'
        self.assertEqual(lint.violations(text), [])

    def test_proved_bounds_and_explicit_results_pass(self):
        text = 'def f (h : i < a.size) := a[i]\ndef g := Except.error .bounds\n'
        self.assertEqual(lint.violations(text), [])


if __name__ == "__main__":
    unittest.main()
