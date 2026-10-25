"""Keep new self-contained Lean checks reachable from their documented entry points."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class MiriTestsRegistrationTests(unittest.TestCase):
    def test_every_runtime_module_is_registered_with_its_execution_mode(self):
        registry = (ROOT / "MiriTests/RuntimeChecks.lean").read_text()
        entries = re.findall(r'\("(MiriTests/[^\"]+\.lean)", (true|false)\)', registry)
        self.assertEqual(len(entries), len({path for path, _ in entries}))
        for name, mode in entries:
            path = ROOT / name
            self.assertTrue(path.is_file(), name)
            source = path.read_text()
            has_main = bool(re.search(r"^def main\b", source, re.MULTILINE))
            self.assertEqual(mode == "true", has_main, name)
            if not has_main:
                self.assertIn("#eval", source, name)
        registered = {name for name, _ in entries}
        for path in (ROOT / "MiriTests").rglob("*.lean"):
            if path.name == "Run.lean":
                continue
            if re.search(r"^def main\b", path.read_text(), re.MULTILINE):
                self.assertIn(path.relative_to(ROOT).as_posix(), registered)

    def test_declaration_modules_participate_in_the_aggregate_axiom_audit(self):
        registry = (ROOT / "MiriTests/RuntimeChecks.lean").read_text()
        runtime_paths = set(re.findall(r'\("(MiriTests/[^\"]+\.lean)",', registry))
        imports = set(re.findall(r"^import (\S+)$", (ROOT / "MiriTests.lean").read_text(), re.MULTILINE))
        expected = set()
        for path in (ROOT / "MiriTests").rglob("*.lean"):
            relative = path.relative_to(ROOT)
            if relative.as_posix() in runtime_paths or path.name in {"Run.lean", "RuntimeChecks.lean", "AxiomAudit.lean"}:
                continue
            expected.add(".".join(relative.with_suffix("").parts))
        self.assertEqual(imports, expected)
        self.assertIn("import MiriTests\n", (ROOT / "MiriTests/AxiomAudit.lean").read_text())
