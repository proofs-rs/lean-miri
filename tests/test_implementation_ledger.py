#!/usr/bin/env python3
"""Fail-closed checks for AST/source/evidence links in the implementation ledger."""

from __future__ import annotations

import copy
import gzip
import json
from pathlib import Path
import subprocess
import sys
import unittest

REPO = Path(__file__).resolve().parents[1]
ROOT = REPO / "scratch/source-audit"
sys.path.insert(0, str(ROOT / "tools"))

from check_implementation_ledger import validate_objects  # noqa: E402


def load_inputs():
    ledger = json.loads((ROOT / "tracking/implementation-ledger.json").read_text())
    with gzip.open(ROOT / "tools/source-analysis/inventory.json.gz", "rt") as stream:
        inventory = json.load(stream)
    source_lock = json.loads((ROOT / "upstream/source-lock.json").read_text())
    return ledger, inventory, source_lock


class ImplementationLedgerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ledger, cls.inventory, cls.source_lock = load_inputs()

    def test_generated_snapshot_is_current(self):
        subprocess.run(
            [sys.executable, str(ROOT / "tools/update_implementation_ledger.py"), "--root", str(ROOT), "--check"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )

    def test_checked_ledger_links_all_reviewed_rows(self):
        report, errors = validate_objects(
            ROOT, self.ledger, self.inventory, self.source_lock
        )
        self.assertEqual(errors, [])
        self.assertIsNone(report["repository_wide_percentage"])
        self.assertEqual(
            sum(row["reviewed_ast_symbols"] for row in report["scope_reports"]),
            len({entry["source"]["ast_symbol_id"] for entry in self.ledger["entries"]}),
        )

    def test_unknown_ast_id_fails_closed(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["source"]["ast_symbol_id"] = "missing::symbol"
        _, errors = validate_objects(ROOT, ledger, self.inventory, self.source_lock)
        self.assertTrue(any("unknown AST symbol id" in error for error in errors))

    def test_source_hash_mismatch_fails_closed(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["source"]["sha256"] = "0" * 64
        _, errors = validate_objects(ROOT, ledger, self.inventory, self.source_lock)
        self.assertTrue(any("source SHA-256 does not match source-lock" in error for error in errors))

    def test_missing_evidence_file_fails_closed(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["evidence"]["files"].append("tests/missing-evidence")
        _, errors = validate_objects(ROOT, ledger, self.inventory, self.source_lock)
        self.assertTrue(any("evidence file is missing" in error for error in errors))

    def test_whole_function_completion_claim_fails_closed(self):
        ledger = copy.deepcopy(self.ledger)
        ledger["entries"][0]["source_function_complete"] = True
        _, errors = validate_objects(ROOT, ledger, self.inventory, self.source_lock)
        self.assertTrue(any("whole-function completion claims are forbidden" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
