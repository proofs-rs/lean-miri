"""Fresh compiler-boundary regressions; missing setup is an error, never a skip."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document, pool_entry


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

    def export(self, fixture, root="identity", environment=None, crate_type="lib"):
        return subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", root, "--",
             str(ROOT / "exporter/fixtures/fail_closed" / f"{fixture}.rs"),
             "--crate-type=" + crate_type, "--crate-name=fail_closed_fixture"],
            cwd=ROOT, env=environment or self.environment, capture_output=True, text=True,
        )

    def accepted(self, fixture, root="identity", crate_type="lib"):
        result = self.export(fixture, root, crate_type=crate_type)
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        self.assertNotIn("completeness", document)
        seen = set()

        def check(value):
            if not isinstance(value, (dict, list)) or id(value) in seen:
                return
            seen.add(id(value))
            if isinstance(value, dict):
                if value.get("status") == "debug_payload":
                    return
                if "status" in value:
                    self.fail(f"semantic payload contains status: {value}")
                for child in value.values():
                    check(child)
            else:
                for child in value:
                    check(child)

        check(document)
        return document

    def test_layout_query_types_keep_runtime_query_demands(self):
        source = ROOT / "upstream/miri-source/tests/pass/unops.rs"
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", "main", "--",
             str(source), "--crate-type=lib", "--crate-name=layout_query_demand"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        demands = {row["input_type_id"] for row in document["compiler_runtime_queries"]["types"]}
        erased_demands = {
            row["layout_query_input_type"] for row in document["types"]
            if row.get("layout_query_input_type") is not None
        }
        self.assertTrue(erased_demands)
        self.assertFalse(erased_demands - demands, "canonical layout-query types lost runtime demand rows")

    def test_nested_foreign_block_is_not_an_ambiguous_mir_root(self):
        self.accepted("nested_foreign_root")
        result = self.export("nested_foreign_root", "missing")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('did not resolve to a local MIR body', result.stderr)

    def test_foreign_repr_c_transfer_records_exact_false_covariance(self):
        document = self.accepted("foreign_repr_c_transfer", crate_type="bin")
        types = {row['display']: row['type_id'] for row in document['types']}
        source, target = types['CallerType'], types['implementation::CalleeType']
        rows = [row for row in document['compiler_covariance_queries']
                if row['source_type'] == source and row['target_type'] == target]
        self.assertEqual(len(rows), 1)
        self.assertIs(rows[0]['value'], False)

    def test_no_std_keeps_negative_and_optional_query_answers(self):
        document = self.accepted("no_std")
        self.assertNotIn("compiler_named_constants", document)
        self.assertNotIn("startup", document["compiler_runtime_queries"])
        unsigned = next(node for node in document["types"]
                        if node["shape"].get("unsigned_kind") == "u32")
        facts = unsigned["compiler_facts"]
        self.assertEqual(facts["boolean_queries"]["is_dynamic"],
                         False)
        self.assertEqual(facts["type_queries"]["boxed_type"],
                         None)

    def test_no_main_binary_exports_startup_facts(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--",
             str(ROOT / "tests/connected/fixtures/203-upcast-a-prefix.rs"),
             "--crate-type=bin", "--crate-name=custom_entry_startup", "-Cpanic=abort"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        self.assertEqual(set(document["compiler_named_types"]), {"c_ulong", "i32_pointer"})
        self.assertIsInstance(document["compiler_named_types"]["c_ulong"], int)
        self.assertNotIn("compiler_named_constants", document)
        startup = document["compiler_runtime_queries"]["startup"]
        self.assertIs(startup["no_core"], False)
        sentinel = startup["core_escape_default"]
        self.assertIs(sentinel["mir_available"], True)
        self.assertIsInstance(pool_entry(document, "definitions", sentinel["definition"])["crate"], int)
        self.assertIsInstance(pool_entry(document, "definitions", sentinel["definition"])["index"], int)

    def test_function_pointer_query_keeps_direct_instance_identity(self):
        document = self.accepted("function_pointer")
        resolutions = [record for record in document["compiler_cast_queries"]
                       if record["query_kind"] == "resolve_fn_ptr"]
        self.assertTrue(resolutions)
        for record in resolutions:
            self.assertNotIn("value", record)
            self.assertEqual(record["resolution_kind"], "instance")
            self.assertIsInstance(record["instance_id"], int)
            instance = pool_entry(document, "instances", record["instance_id"])
            self.assertIn("instance_kind", instance)
            self.assertIn("generic_args", instance)
            self.assertNotIn("instance_kind", record)
            self.assertNotIn("generic_args", record)

    def test_std_main_box_constructor_retains_numeric_result(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--",
             str(ROOT / "tests/repro/startup/empty-main.rs"), "--crate-type=bin",
             "--crate-name=box_query_main", "-Cpanic=abort"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        queries = [row for row in document["compiler_cast_queries"]
                   if row["query_kind"] == "box_type"]
        self.assertTrue(queries)
        for row in queries:
            self.assertIsInstance(row["type"], int)
            self.assertIsInstance(row["input_type"], int)
            boxed = pool_entry(document, "types", row["type"])
            self.assertEqual(boxed["shape"]["kind"], "adt")
            self.assertIn("Box", boxed["shape"]["def_path"])

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

    def test_resolved_generic_has_one_body_and_no_source_constant_payload(self):
        document = self.accepted("resolved_generic", "root")
        bodies = document["bodies"]
        self.assertEqual(len({(body["instance_id"], body.get("source_promoted"))
                              for body in bodies}), len(bodies))
        resolved = [row for row in document["instances"]
                    if row.get("def_path", "").endswith("resolved")]
        self.assertTrue(resolved)
        body = pool_entry(document, "bodies", resolved[0]["body"])
        self.assertEqual(body["instance_id"], resolved[0]["instance_id"])
        self.assertTrue(any(pool_entry(document, "types", local["type"])["shape"].get("kind")
                            == "raw_pointer" for local in body["locals"]))

        def inspect(value):
            if isinstance(value, dict):
                self.assertNotIn("constant_query_context", value)
                self.assertNotIn("source_body_is_polymorphic", value)
                if value.get("kind") == "evaluated_const":
                    self.assertEqual(set(value), {"kind", "value"})
                for child in value.values():
                    inspect(child)
            elif isinstance(value, list):
                for child in value:
                    inspect(child)

        inspect(document)

    def test_unused_required_constant_failure_aborts_without_output(self):
        result = self.export("unused_required_const", "root")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("evaluation", result.stderr.lower())
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
