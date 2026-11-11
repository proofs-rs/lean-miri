"""Fresh compiler-boundary regressions; missing setup is an error, never a skip."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


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

    def test_llvm_intrinsics_have_typed_no_abi_evidence(self):
        document = self.accepted("llvm_no_abi")
        calls = [block["terminator"]["kind"]["resolution"]
                 for body in document["bodies"] for block in body["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        llvm = [call for call in calls if call["kind"] == "llvm_intrinsic"]
        self.assertEqual(len(llvm), 2)
        ids = {call["instance_id"] for call in llvm}
        for call in llvm:
            self.assertNotIn("fn_abi", call)
            self.assertNotIn("dispatch_slot", call)
            instance = document["instances"][call["instance_id"]]
            self.assertEqual(instance["instance_kind"]["kind"], "llvm_intrinsic")
        queries = document["compiler_instance_abis"]
        self.assertFalse(ids & {row["instance_id"] for row in queries})

    def test_source_llvm_abi_keeps_signature_without_synthetic_normal_abi(self):
        for fixture in ("llvm_source_abi", "llvm_stdarch_abi"):
            with self.subTest(fixture=fixture):
                document = self.accepted(fixture)
                facts = document["compiler_function_facts"]
                llvm = [row for row in facts["types"]
                        if row["signature_query"]["abi"]["kind"] == "llvm_intrinsic"]
                self.assertTrue(llvm, "fixture must use the actual stdarch LLVM ABI")
                helpers = facts["helper_signatures"]
                self.assertFalse(any(row["signature"]["abi"]["kind"] == "llvm_intrinsic" for row in helpers))
                for row in llvm:
                    signature = row["signature_query"]
                    self.assertTrue(any(helper["signature"]["abi"]["kind"] == "rust"
                                        and helper["signature"]["inputs"] == signature["inputs"]
                                        and helper["signature"]["output"] == signature["output"]
                                        for helper in helpers), "valid Rust helper candidate was dropped")

    def test_uncalled_llvm_pointer_preserves_metadata_without_undefined_abi(self):
        document = self.accepted("llvm_pointer_metadata")
        facts = document["compiler_function_facts"]
        pointers = {row["type_id"] for row in facts["types"]
                    if row["function_kind"]["kind"] == "function_pointer"
                    and row["signature_query"]["abi"]["kind"] == "llvm_intrinsic"}
        self.assertTrue(pointers, "fixture must retain the LLVM ABI pointer type")
        self.assertFalse(pointers & {row["type_id"] for row in facts["pointer_abis"]})
        for ty in pointers:
            self.assertIsInstance(document["types"][ty]["layout"], int)

    def test_demanded_llvm_pointer_abi_fails_closed_without_panicking(self):
        result = self.export("llvm_pointer_call")
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("FnPtr ABI query is not defined for LLVM intrinsic signatures", result.stderr)
        self.assertNotIn("panicked", result.stderr)
        self.assertFalse(self.output.exists())

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
        self.assertIn("MIR: coroutine layout serialization is not implemented", result.stderr)
        self.assertNotIn("TooGeneric", result.stderr)
        self.assertNotIn("reported compilation errors", result.stderr)
        self.assertFalse(self.output.exists())

    def test_concrete_async_return_abi_exports_before_polling_coroutine(self):
        document = self.accepted("runtime_async_abi", "root")
        instance = next(row for row in document["instances"]
                        if row["def_path"] == "make_future")
        queries = [row for row in document["compiler_instance_abis"]
                   if row["instance_id"] == instance["instance_id"]
                   and row["extra_argument_types"] == []]
        self.assertEqual(len(queries), 1)
        self.assertEqual(queries[0]["typing_env"], "fully_monomorphized")
        abi = pool_entry(document, "fn_abis", queries[0]["abi_query"])
        returned = pool_entry(document, "types", abi["return"]["type"])
        self.assertEqual(returned["shape"]["kind"], "coroutine")
        root = pool_entry(document, "bodies", document["body_roots"][0]["body"])
        calls = [block["terminator"]["kind"] for block in root["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        calls = [call for call in calls
                 if call["resolution"].get("instance_id") == instance["instance_id"]]
        self.assertTrue(calls, "fixture must call the concrete async constructor")
        self.assertTrue(all(call["resolution"]["fn_abi"] == queries[0]["abi_query"]
                            for call in calls))

    def test_nested_signature_regions_keep_source_identity_and_closed_query_view(self):
        document = self.accepted("higher_ranked_variadic", "root")
        enclosing = [row for row in document["types"]
                     if row["shape"].get("kind") == "reference"
                     and row["shape"]["region"].get("kind") == "bound"
                     and row["shape"]["region"]["index_kind"]["debruijn_index"] == 1
                     and "va_arg::" in row["shape"]["region"]["bound_kind"].get("def_path", "")]
        self.assertTrue(enclosing, "fixture must preserve the enclosing VaList region Binder")
        function_facts = {row["type_id"] for row in document["compiler_function_facts"]["types"]}
        runtime_demands = {row["input_type_id"]
                           for row in document["compiler_runtime_queries"]["types"]}
        for source in enclosing:
            query_id = source["layout_query_input_type"]
            query = pool_entry(document, "types", query_id)
            self.assertNotEqual(source["type_id"], query_id)
            self.assertEqual(query["shape"]["region"], {"kind": "erased"})
            self.assertEqual(source["layout"], query["layout"])
            self.assertEqual(source["compiler_facts"], query["compiler_facts"])
            self.assertIn(query_id, runtime_demands)
            pointers = [row for row in document["types"]
                        if row["shape"].get("kind") == "function_pointer"
                        and row["shape"]["signature"]["output"] == source["type_id"]]
            self.assertTrue(pointers, "source signature must still reference its original bound region")
            for pointer in pointers:
                closed_id = pointer["layout_query_input_type"]
                closed = pool_entry(document, "types", closed_id)
                self.assertEqual(closed["shape"]["signature"]["output"], query_id)
                self.assertNotIn(pointer["type_id"], function_facts)
                self.assertIn(closed_id, function_facts)
                self.assertIn(closed_id, runtime_demands)

    def test_variadic_fixed_count_mismatch_keeps_target_extra_argument_abi(self):
        # This guest would be UB. Export must retain the exact query needed
        # to report that mismatch, rather than stopping at missing metadata.
        document = self.accepted("variadic_fixed_count_mismatch", "root")
        callee = next(row for row in document["instances"]
                      if row["def_path"] == "callee")
        rows = [row for row in document["compiler_instance_abis"]
                if row["instance_id"] == callee["instance_id"]
                and len(row["extra_argument_types"]) == 1]
        self.assertEqual(len(rows), 1)
        extra = pool_entry(document, "types", rows[0]["extra_argument_types"][0])
        self.assertEqual(extra["shape"], {"kind": "int", "signed_kind": "i32"})
        callee_abi = pool_entry(document, "fn_abis", rows[0]["abi_query"])
        self.assertTrue(callee_abi["c_variadic"])
        self.assertEqual(callee_abi["fixed_count"], 1)
        self.assertEqual(len(callee_abi["arguments"]), 2)
        caller_rows = [row for row in document["compiler_function_facts"]["pointer_abis"]
                       if row["extra_argument_types"] == rows[0]["extra_argument_types"]]
        caller_abis = [pool_entry(document, "fn_abis", row["abi_query"]) for row in caller_rows]
        self.assertTrue(any(abi["c_variadic"] and abi["fixed_count"] == 0
                            and len(abi["arguments"]) == 1 for abi in caller_abis),
                        "the actual caller/callee fixed-count mismatch must remain visible")

    def test_resolved_generic_has_one_body_and_no_source_constant_payload(self):
        document = self.accepted("resolved_generic", "root")
        bodies = document["bodies"]
        self.assertEqual(len({body["instance_id"] for body in bodies}), len(bodies))
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

    def test_ignored_body_fields_are_not_serialized(self):
        document = self.accepted("resolved_generic", "root")
        removed = {"source_instance_kind", "source_promoted", "pass_count", "tainted_by_errors",
                   "var_debug_info", "mentioned_items", "user_type_annotations", "coroutine_info"}
        for body in document["bodies"]:
            self.assertFalse(removed & body.keys())
            self.assertIn("required_consts", body)
            for local in body["locals"]:
                self.assertFalse({"local_info", "mutability", "layout"} & local.keys())
            for scope in body["source_scopes"]:
                self.assertNotIn("local_data", scope)

    def test_typecheck_errors_abort_without_export_output(self):
        result = self.export("typeck_error")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("mismatched types", result.stderr)
        self.assertIn("pinned rustc driver reported compilation errors", result.stderr)
        self.assertFalse(self.output.exists())

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
