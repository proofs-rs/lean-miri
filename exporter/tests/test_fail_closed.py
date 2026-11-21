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
        toolchain = rustup / "toolchains/miri-exporter-8eb778d04094"
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
        self.assertEqual(document["schema_version"], 17)
        for name in ("layouts", "layout_values", "fn_abis", "abi_arguments", "boolean_queries",
                     "discriminants", "compiler_instance_abis", "compiler_function_facts",
                     "compiler_covariance_queries", "compiler_vtable_queries", "compiler_cast_queries"):
            self.assertNotIn(name, document)
        for node in document["types"]:
            self.assertFalse({"layout", "layout_query_input_type", "compiler_facts"} & node.keys())
        for intrinsic in document["instances"]:
            if intrinsic["instance_kind"]["kind"] != "intrinsic":
                continue
            items = [row for row in document["instances"]
                     if row["instance_kind"]["kind"] == "item"
                     and row["def_id"] == intrinsic["def_id"]
                     and row["generic_args"] == intrinsic["generic_args"]]
            self.assertEqual(len(items), 1, "Miri intrinsic ABI needs its exact Item identity")
            item = items[0]
            self.assertIsNotNone(document["source_abi"]["definitions"][item["instance_id"]])
            if intrinsic["fallback_instance"] is None:
                self.assertEqual(item["kind"], "identity_only", "ABI-only Item must not emit MIR")
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

    def test_x87_wrapper_and_raw_type_have_distinct_source_material(self):
        document = self.accepted("x87_source", root="root")
        wrappers = [node for node in document["types"] if node["source_layout"]["is_x87_f80"]]
        raw = [node for node in document["types"] if node["source_layout"]["special_float"] == "x87_f80"]
        self.assertEqual(len(wrappers), 1)
        self.assertEqual(len(raw), 1)
        self.assertIsNone(wrappers[0]["source_layout"]["special_float"])
        self.assertFalse(raw[0]["source_layout"]["is_x87_f80"])
        self.assertEqual(wrappers[0]["shape"]["variants"][0]["fields"][0]["type"], raw[0]["type_id"])
        self.assertEqual(document["runtime_target_data_layout"]["x87_f80_align_bytes"], 16)

    def test_aarch64_scalable_vector_material_preserves_eight_parts(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", "root", "--",
             str(ROOT / "exporter/fixtures/fail_closed/scalable_source.rs"),
             "--target=aarch64-unknown-linux-gnu", "-Ctarget-feature=+sve",
             "--crate-type=lib", "--crate-name=scalable_source"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        parts = {node["display"]: node["source_layout"]["scalable_vectors"]
                 for node in document["types"] if node["source_layout"]["scalable_vectors"] is not None}
        self.assertEqual(parts, {"Vector8": 8, "Vector": 1})

    def test_llvm_intrinsics_keep_exact_identity_without_abi_results(self):
        document = self.accepted("llvm_no_abi")
        calls = [block["terminator"]["kind"]["resolution"]
                 for body in document["bodies"] for block in body["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        llvm = [call for call in calls if call["kind"] == "llvm_intrinsic"]
        self.assertEqual(len(llvm), 2)
        ids = {call["instance_id"] for call in llvm}
        for call in llvm:
            self.assertNotIn("fn_abi", call)
            instance = document["instances"][call["instance_id"]]
            self.assertEqual(instance["instance_kind"]["kind"], "llvm_intrinsic")
        self.assertFalse(ids & {row["instance_id"] for row in document["source_abi"]["definitions"]})

    def test_source_llvm_abi_keeps_its_original_signature(self):
        for fixture in ("llvm_source_abi", "llvm_stdarch_abi"):
            with self.subTest(fixture=fixture):
                document = self.accepted(fixture)
                signatures = [row["shape"]["signature"] for row in document["types"]
                              if row["shape"].get("kind") in ("function_definition", "function_pointer")]
                self.assertTrue(any(signature["abi"]["kind"] == "llvm_intrinsic"
                                    for signature in signatures))

    def test_uncalled_llvm_pointer_keeps_source_type(self):
        document = self.accepted("llvm_pointer_metadata")
        pointers = [row for row in document["types"]
                    if row["shape"].get("kind") == "function_pointer"
                    and row["shape"]["signature"]["abi"]["kind"] == "llvm_intrinsic"]
        self.assertTrue(pointers)
        for pointer in pointers:
            self.assertIsInstance(pointer["source_layout"]["normalized_type"], int)

    def test_llvm_pointer_call_defers_abi_to_the_consumer(self):
        document = self.accepted("llvm_pointer_call")
        calls = [block["terminator"]["kind"]["resolution"]
                 for body in document["bodies"] for block in body["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        self.assertTrue(any(call["kind"] == "indirect_function_pointer"
                            and call["signature"]["abi"]["kind"] == "llvm_intrinsic"
                            for call in calls))

    def test_normalized_runtime_views_are_defined_source_types(self):
        source = ROOT / "upstream/miri-source/tests/pass/unops.rs"
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", "main", "--",
             str(source), "--crate-type=lib", "--crate-name=normalization_material"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        for node in document["types"]:
            normalized = pool_entry(document, "types", node["source_layout"]["normalized_type"])
            self.assertEqual(normalized["source_layout"]["normalized_type"], normalized["type_id"])

    def test_nested_foreign_block_is_not_an_ambiguous_mir_root(self):
        self.accepted("nested_foreign_root")
        result = self.export("nested_foreign_root", "missing")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('did not resolve to a local MIR body', result.stderr)

    def test_foreign_repr_c_transfer_preserves_nominal_type_difference(self):
        document = self.accepted("foreign_repr_c_transfer", crate_type="bin")
        types = {row["display"]: row for row in document["types"]}
        source, target = types["CallerType"], types["implementation::CalleeType"]
        self.assertNotEqual(source["shape"]["def_id"], target["shape"]["def_id"])
        for node in (source, target):
            self.assertTrue(node["shape"]["representation"]["flags_bits"] & 1)
            self.assertEqual(len(node["shape"]["variants"][0]["fields"]), 1)

    def test_shared_reborrow_keeps_both_nominal_type_definitions(self):
        document = self.accepted("shared_reborrow")
        reborrows = []
        def visit(value):
            if isinstance(value, dict):
                if value.get("kind") == "Reborrow" and value["mutability"]["kind"] == "immutable":
                    reborrows.append(value)
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)
        visit(document["bodies"])
        self.assertTrue(reborrows)
        for value in reborrows:
            source = pool_entry(document, "types", value["place"]["type"])
            target = pool_entry(document, "types", value["type"])
            self.assertNotEqual(source["shape"]["def_id"], target["shape"]["def_id"])
            self.assertEqual(source["source_layout"]["variances"],
                             [{"kind": "covariant"}, {"kind": "invariant"}])
            self.assertEqual(target["source_layout"]["variances"],
                             [{"kind": "covariant"}, {"kind": "covariant"}])

    def test_no_std_keeps_negative_and_optional_declaration_fields(self):
        document = self.accepted("no_std")
        self.assertNotIn("compiler_named_constants", document)
        self.assertNotIn("startup", document["compiler_runtime_queries"])
        unsigned = next(node for node in document["types"]
                        if node["shape"].get("unsigned_kind") == "u32")
        self.assertIs(unsigned["source_layout"]["is_box"], False)
        self.assertIsNone(unsigned["source_layout"]["simd"])
        self.assertEqual(unsigned["source_layout"]["normalized_type"], unsigned["type_id"])

    def test_no_main_binary_exports_startup_facts(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", "miri_start", "--",
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

    def test_function_pointer_material_keeps_direct_instance_identity(self):
        document = self.accepted("function_pointer")
        resolutions = [record for record in document["source_cast_targets"]
                       if record["kind"] == "function_pointer"]
        self.assertTrue(resolutions)
        for record in resolutions:
            self.assertIsInstance(record["instance_id"], int)
            instance = pool_entry(document, "instances", record["instance_id"])
            self.assertIn("instance_kind", instance)
            self.assertIn("generic_args", instance)
            self.assertNotIn("instance_kind", record)

    def test_std_main_keeps_finite_box_type_material(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--root", "main", "--",
             str(ROOT / "tests/repro/startup/empty-main.rs"), "--crate-type=bin",
             "--crate-name=box_material_main", "-Cpanic=abort"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        document = load_mir_document(self.output)
        boxes = [node for node in document["types"] if node["source_layout"]["is_box"]]
        self.assertTrue(boxes)
        self.assertTrue(all(node["shape"]["kind"] == "adt" and node["shape"]["generic_args"]
                            for node in boxes))
        for node in boxes:
            normalized = document["types"][node["source_layout"]["normalized_type"]]
            pointee = normalized["shape"]["generic_args"][0]["value"]
            pointers = [candidate for candidate in document["types"]
                        if candidate["shape"].get("kind") == "raw_pointer"
                        and candidate["shape"].get("mutability", {}).get("kind") == "mutable"
                        and candidate["shape"].get("pointee") == pointee]
            self.assertEqual(len(pointers), 1, f"missing or ambiguous Box pointer for {node['display']}")

    def test_result_main_has_exact_bootstrap_source_signature(self):
        document = self.accepted("start_result", "main", "bin")
        main = next(row for row in document["compiler_main_queries"]["entries"]
                    if row["signature_query"]["compiler_selected_entry"])
        primitive = document["compiler_runtime_primitives"]
        types = document["types"]
        def const_pointer_to(ty):
            return next(row["type_id"] for row in types
                        if row["shape"]["kind"] == "raw_pointer"
                        and row["shape"]["mutability"]["kind"] == "immutable"
                        and row["shape"]["pointee"] == ty)
        argv = const_pointer_to(const_pointer_to(primitive["u8"]))
        entry_pointer = types[main["signature_query"]["function_pointer_type"]]["source_layout"]["normalized_type"]
        expected = [entry_pointer,
                    primitive["isize"], argv, primitive["u8"]]
        start = main["signature_query"]["start_resolution"]["instance_id"]
        signature = next(row["signature"] for row in document["source_abi"]["definitions"]
                         if row["instance_id"] == start)
        self.assertEqual(signature["inputs"], expected)
        self.assertEqual(signature["output"], primitive["isize"])
        self.assertEqual(signature["abi"]["kind"], "rust")
        self.assertFalse(signature["c_variadic"])

    def test_weak_static_function_demands_keep_exact_source_recipes(self):
        for fixture, name, args, ret in [
            ("weak_getrandom", "getrandom", ["pointer", "usize", "u32"], "isize"),
            ("weak_cxa", "__cxa_thread_atexit_impl", ["pointer"] * 3, "i32"),
        ]:
            with self.subTest(fixture=fixture):
                document = self.accepted(fixture)
                recipe = next(row["recipe"] for row in document["compiler_named_shim_abis"]
                              if row["name"] == name)
                self.assertEqual(recipe["signature"]["arguments"], args)
                self.assertEqual(recipe["signature"]["return"], ret)
                self.assertEqual(len(recipe["input_types"]), len(args))
                self.assertIsInstance(recipe["output_type"], int)

    def test_unknown_weak_static_does_not_synthesize_named_shim(self):
        document = self.accepted("weak_unknown")
        self.assertNotIn("lean_miri_unknown_weak", {
            row["name"] for row in document.get("compiler_named_shim_abis", [])})

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
        pointers = next(node for node in document["allocations"]
                        if node.get("def_path") == "POINTERS")
        value = next(node for node in document["allocations"]
                     if node.get("def_path") == "VALUE")
        self.assertEqual(pointers["kind"], "static")
        self.assertEqual(value["kind"], "static")
        self.assertNotEqual(pointers["allocation_id"], value["allocation_id"])
        self.assertNotEqual(pointers["source_alloc_id"], value["source_alloc_id"])
        self.assertEqual(pointers["initializer"]["relocations"], [{
            "storage_offset_bytes": 0, "target": value["allocation_id"],
            "target_offset_encoded_bytes": "0000000000000000",
            "immutable": True, "shared_ref": True}])

    def test_required_foreign_tls_initializer_aborts_without_output(self):
        result = self.export("foreign_tls", "read_external")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("foreign thread-local initializer is unavailable", result.stderr)
        self.assertFalse(self.output.exists())

    def test_coroutine_metadata_retains_exact_coverage_and_runtime_abi(self):
        document = self.accepted("coroutine", "root")
        self.assertEqual(document["schema_version"], 17)
        coverage = document["compiler_coroutine_coverage"]
        self.assertTrue(coverage["coroutines"])
        self.assertEqual(len(coverage["body_coroutines"]), len(document["bodies"]))
        owners = {document["bodies"][row["owner_body"]]["instance_id"] for row in coverage["coroutines"]}
        self.assertTrue(owners <= {row["instance_id"] for row in document["source_abi"]["definitions"]})
        self.assertFalse(owners & {row["instance_id"] for row in document["compiler_native_signature_queries"]})
        for row in coverage["coroutines"]:
            self.assertIsNone(row["yield_type"])
            self.assertIsNone(row["resume_type"])
            self.assertGreaterEqual(len(row["layout"]["variant_fields"]), 3)
            for key, role in (("drop_sync", "sync"), ("drop_async", "async"), ("drop_proxy_async", "proxy_async")):
                if row[key] is not None:
                    auxiliary = coverage["auxiliary_bodies"][row[key]]
                    self.assertEqual(auxiliary["owner_body"], row["owner_body"])
                    self.assertEqual(auxiliary["role"], role)
                    self.assertEqual(auxiliary["source_kind"]["def_id"], auxiliary["body"]["source_def_id"])

    def test_concrete_coroutine_layout_constant_uses_runtime_ecx(self):
        document = self.accepted("coroutine_box_layout", "root")
        self.assertTrue(document["compiler_coroutine_coverage"]["coroutines"])
        self.assertTrue(any(row["query"] == "instantiate_bound_regions_with_erased(closure_args.sig())"
                            for row in document["compiler_native_signature_queries"]),
                        "normal closure FnSig facts must survive the coroutine domain refinement")
        boxes = [row for row in document["instances"] if row.get("def_path", "").endswith("::new") and "boxed" in row.get("def_path", "")]
        self.assertTrue(boxes, "control must instantiate Box::new<Coroutine>")
        layout_types = {row["type_id"] for row in document["types"]
                        if row.get("shape", {}).get("kind") == "adt"
                        and row["shape"].get("def_path") == "std::alloc::Layout"}
        evaluated_layouts = []
        def inspect(value):
            if isinstance(value, dict):
                constant = value.get("constant")
                if type(value.get("type")) is int and value["type"] in layout_types and isinstance(constant, dict) and constant.get("kind") == "evaluated_const":
                    evaluated_layouts.append(constant["value"])
                for child in value.values():
                    inspect(child)
            elif isinstance(value, list):
                for child in value:
                    inspect(child)
        for instance in boxes:
            body = document["bodies"][instance["body"]]
            self.assertEqual(body["phase"]["kind"], "runtime")
            inspect(body)
        self.assertTrue(evaluated_layouts, "Box::new must retain its compiler-evaluated Layout operand")

    def test_generic_root_does_not_evaluate_symbolic_runtime_constants(self):
        document = self.accepted("generic_runtime_constant", "root")
        self.assertEqual(document["bodies"], [])
        self.assertEqual(document["root_declarations"][0]["def_path"], "root")

    def test_concrete_async_constructor_keeps_its_normalized_source_signature(self):
        document = self.accepted("runtime_async_abi", "root")
        instance = next(row for row in document["instances"] if row["def_path"] == "make_future")
        definition = next(row for row in document["source_abi"]["definitions"]
                          if row["instance_id"] == instance["instance_id"])
        returned = pool_entry(document, "types", definition["signature"]["output"])
        self.assertEqual(returned["shape"]["kind"], "coroutine")
        root = pool_entry(document, "bodies", document["body_roots"][0]["body"])
        calls = [block["terminator"]["kind"] for block in root["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        self.assertTrue(any(call["resolution"].get("instance_id") == instance["instance_id"]
                            for call in calls))

    def test_nested_signature_regions_keep_source_binders_and_normalized_view(self):
        document = self.accepted("higher_ranked_variadic", "root")
        enclosing = [row for row in document["types"]
                     if row["shape"].get("kind") == "reference"
                     and row["shape"]["region"].get("kind") == "bound"
                     and row["shape"]["region"]["index_kind"]["debruijn_index"] == 1
                     and "va_arg::" in row["shape"]["region"]["bound_kind"].get("def_path", "")]
        self.assertTrue(enclosing)
        for source in enclosing:
            runtime_id = source["source_layout"]["normalized_type"]
            runtime = pool_entry(document, "types", runtime_id)
            self.assertNotEqual(source["type_id"], runtime_id)
            self.assertEqual(runtime["shape"]["region"], {"kind": "erased"})
            pointers = [row for row in document["types"]
                        if row["shape"].get("kind") == "function_pointer"
                        and row["shape"]["signature"]["output"] == source["type_id"]]
            self.assertTrue(pointers)
            for pointer in pointers:
                closed = pool_entry(document, "types", pointer["source_layout"]["normalized_type"])
                self.assertEqual(closed["shape"]["signature"]["output"], runtime_id)

    def test_variadic_fixed_count_mismatch_keeps_exact_call_inputs(self):
        document = self.accepted("variadic_fixed_count_mismatch", "root")
        callee = next(row for row in document["instances"] if row["def_path"] == "callee")
        signature = next(row["signature"] for row in document["source_abi"]["definitions"]
                         if row["instance_id"] == callee["instance_id"])
        self.assertTrue(signature["c_variadic"])
        self.assertEqual(len(signature["inputs"]), 1)
        calls = [block["terminator"]["kind"]["resolution"]
                 for body in document["bodies"] for block in body["basic_blocks"]
                 if block["terminator"]["kind"].get("variant") == "Call"]
        caller = next(call for call in calls if call["kind"] == "indirect_function_pointer")
        self.assertTrue(caller["signature"]["c_variadic"])
        self.assertEqual(caller["signature"]["inputs"], [])
        self.assertEqual(len(caller["extra_argument_types"]), 1)
        extra = pool_entry(document, "types", caller["extra_argument_types"][0])
        self.assertEqual(extra["shape"], {"kind": "int", "signed_kind": "i32"})

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

    def test_concrete_closure_excludes_query_only_functions_and_drops(self):
        document = self.accepted("concrete_closure", "root")
        executable = [instance for instance in document["instances"]
                      if instance["kind"] == "instance_mir"]
        self.assertEqual({instance["def_path"] for instance in executable},
                         {"root", "identity"})
        identity = next(instance for instance in executable
                        if instance["def_path"] == "identity")
        self.assertEqual(len(identity["generic_args"]), 1)
        argument = identity["generic_args"][0]
        self.assertEqual(argument["kind"], "type")
        self.assertEqual(pool_entry(document, "types", argument["value"])["shape"],
                         {"kind": "uint", "unsigned_kind": "u32"})
        self.assertEqual(len(document["bodies"]), 2)

    def test_concrete_closure_keeps_actual_function_pointer_targets(self):
        document = self.accepted("concrete_closure", "pointer_root")
        executable = [instance for instance in document["instances"]
                      if instance["kind"] == "instance_mir"]
        self.assertEqual({instance["def_path"] for instance in executable},
                         {"pointer_root", "uncalled"})

    def test_library_export_requires_explicit_roots(self):
        result = subprocess.run(
            [str(self.exporter), "--output", str(self.output), "--",
             str(ROOT / "exporter/fixtures/fail_closed/concrete_closure.rs"),
             "--crate-type=lib", "--crate-name=explicit_roots"],
            cwd=ROOT, env=self.environment, capture_output=True, text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires at least one --root", result.stderr)
        self.assertFalse(self.output.exists())

    def test_generic_root_exports_only_its_declaration(self):
        document = self.accepted("concrete_closure", "identity")
        self.assertEqual(document["bodies"], [])
        self.assertEqual(document["body_roots"], [])
        declarations = document["root_declarations"]
        self.assertEqual(len(declarations), 1)
        self.assertEqual(declarations[0]["def_path"], "identity")
        self.assertEqual(declarations[0]["generic_parameters"], ["type"])

    def test_concrete_vtable_bindings_reach_supertrait_methods(self):
        document = self.accepted("concrete_vtable", "root")
        source = document["source_vtables"]
        principals = {pool_entry(document, "predicates", item["principal"])["def_path"]
                      for item in source["object_traits"]}
        self.assertEqual(principals, {"Both", "Base", "Side", "core::marker::MetaSized"})
        self.assertEqual(len(source["bindings"]), 4)
        methods = [method for binding in source["bindings"]
                   for method in binding["methods"]]
        self.assertEqual(len(methods), 2)
        self.assertTrue(all(method["instance_id"] is not None for method in methods))
        for method in methods:
            instance = pool_entry(document, "instances", method["instance_id"])
            self.assertEqual(instance["kind"], "instance_mir")
        for binding in source["bindings"]:
            drop = pool_entry(document, "instances", binding["drop_instance"])
            self.assertEqual(drop["instance_kind"]["shim_kind"], "drop_glue")
            self.assertEqual(drop["kind"], "instance_mir")

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
