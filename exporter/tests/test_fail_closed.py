"""Fresh compiler-boundary regressions; missing setup is an error, never a skip."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document


class FailClosedExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.exporter = Path(os.environ.get(
            "EXPORTER_BIN", ROOT / "exporter/target/debug/lean-miri-mir-exporter"
        )).resolve()
        rustup = Path(os.environ.get("RUSTUP_HOME", ROOT / ".rustup"))
        toolchain = rustup / "toolchains/miri-exporter-8144389c895d"
        cls.environment = dict(os.environ)
        cls.environment["PATH"] = f"{toolchain / 'bin'}:{os.environ['PATH']}"
        cls.environment["LD_LIBRARY_PATH"] = f"{toolchain / 'lib'}:{os.environ.get('LD_LIBRARY_PATH', '')}"
        cls.environment["MIRI_SYSROOT"] = os.environ.get(
            "MIRI_SYSROOT", str(ROOT / "scratch/miri-sysroot")
        )
        cls.environment["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "0"
        cls.environment["LEAN_MIRI_RUN_PREPARED_MIRI"] = "0"
        if not cls.exporter.is_file() or not (toolchain / "bin/rustc").is_file():
            raise RuntimeError("build the exporter and install its pinned Rust toolchain first")

    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="lean-miri-fail-closed-")
        self.addCleanup(self.directory.cleanup)
        self.output = Path(self.directory.name) / "output.json"

    def export(self, fixture, root="identity", environment=None):
        return subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", root, "--",
             str(ROOT / "exporter/fixtures/fail_closed" / f"{fixture}.rs"),
             "--crate-type=lib", "--crate-name=fail_closed_fixture"],
            cwd=ROOT, env=environment or self.environment, capture_output=True, text=True,
        )

    def accepted(self, fixture, root="identity"):
        result = self.export(fixture, root)
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        self.assertEqual(document["completeness"], {"status": "complete"})
        seen = set()

        def check(value):
            if not isinstance(value, (dict, list)) or id(value) in seen:
                return
            seen.add(id(value))
            if isinstance(value, dict):
                if value.get("status") == "debug_payload":
                    return
                if "status" in value:
                    self.assertIn(value["status"], {"supported", "complete"})
                for child in value.values():
                    check(child)
            else:
                for child in value:
                    check(child)

        check(document)
        return document

    def test_no_std_keeps_negative_and_optional_query_answers(self):
        document = self.accepted("no_std")
        self.assertNotIn("compiler_named_constants", document)
        self.assertNotIn("startup", document["compiler_runtime_queries"])
        unsigned = next(node for node in document["types"]
                        if node["shape"].get("unsigned_kind") == "u32")
        facts = unsigned["compiler_facts"]
        self.assertEqual(facts["boolean_queries"]["is_dynamic"],
                         {"status": "supported", "value": False})
        self.assertEqual(facts["type_queries"]["boxed_type"],
                         {"status": "supported", "value": None})

    def test_dynamic_lookup_closes_over_source_allowed_targets(self):
        document = self.accepted("dynamic_symbols")
        names = {row["name"] for row in document["compiler_named_shim_abis"]}
        self.assertTrue({"dlsym", "getrandom", "getentropy"}.issubset(names))
        self.assertNotIn("getpid", names)

    def test_no_core_does_not_request_libcore_or_os_shims(self):
        document = self.accepted("no_core")
        self.assertNotIn("compiler_named_types", document)
        self.assertNotIn("caller_location_type", document["compiler_runtime_primitives"])

    def test_portable_memory_shim_requests_abis_without_os_catalogs(self):
        document = self.accepted("portable_memory")
        self.assertTrue(document["compiler_shim_abis"])
        self.assertNotIn("compiler_named_constants", document)
        self.assertNotIn("compiler_libc_type_layouts", document)

    def test_no_core_miri_shim_keeps_rust_abis_without_core_allocator_types(self):
        document = self.accepted("no_core_shim")
        recipes = document["compiler_shim_abis"]
        self.assertTrue(any(row["signature"]["calling_convention"] == "Rust"
                            for row in recipes))
        self.assertFalse(any("alignment" in row["signature"]["arguments"]
                             for row in recipes))
        self.assertNotIn("compiler_named_types", document)

    def test_allocation_identity_and_relocations_are_preserved(self):
        document = self.accepted("relocations", "ptr")
        images = [node for node in document["allocations"] if node["kind"] == "memory"]
        self.assertTrue(any(node["relocations"] for node in images))

    def test_required_foreign_tls_initializer_aborts_without_output(self):
        result = self.export("foreign_tls", "read_external")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("foreign thread-local initializer is unavailable", result.stderr)
        self.assertFalse(self.output.exists())

    def test_unimplemented_coroutine_metadata_aborts_without_output(self):
        result = self.export("coroutine", "root")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("lean-miri-mir-exporter:", result.stderr)
        self.assertIn("coroutine", result.stderr)
        self.assertNotIn("reported compilation errors", result.stderr)
        self.assertFalse(self.output.exists())

    def test_producer_hash_failure_aborts_without_output(self):
        commands = Path(self.directory.name) / "commands"
        commands.mkdir()
        digest = commands / "sha256sum"
        digest.write_text("#!/bin/sh\necho injected-digest-failure >&2\nexit 23\n")
        digest.chmod(0o755)
        environment = dict(self.environment)
        environment["PATH"] = f"{commands}:{environment['PATH']}"
        result = self.export("no_std", environment=environment)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("injected-digest-failure", result.stderr)
        self.assertFalse(self.output.exists())


if __name__ == "__main__":
    unittest.main()
