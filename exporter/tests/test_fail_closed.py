"""Fresh compiler-boundary regressions; missing setup is an error, never a skip."""

import os
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def raw_body_source(document, body):
    """Inspect the encoded source in its own role; never instantiate its MIR."""
    assert body["body_kind"] == "copy_template"
    assert set(body) == {"body_kind", "template_id", "instance_id", "generic_args", "promoted_bodies"}
    instance = pool_entry(document, "instances", body["instance_id"])
    assert instance["instance_kind"] == {"kind": "item", "def_id": instance["def_id"]}
    assert pool_entry(document, "bodies", instance["body"]) == body
    assert body["generic_args"] == instance["generic_args"] and body["promoted_bodies"] == []
    source = document["mir_templates"][body["template_id"]]
    assert source["source_def_id"] == instance["def_id"] and source["def_path"] == instance["def_path"]
    assert source["source_role"] == "runtime" and source["source_promoted"] is None
    assert source["injection_phase"] is None
    template = json.loads(source["template"])
    assert template["parameters"] == [{"type": "type", "const": "constant", "lifetime": "region"}[a["kind"]]
                                      for a in body["generic_args"]]
    skeleton = template["skeleton"]
    assert skeleton["phase"] == "runtime_optimized"
    assert len(source["local_sources"]) == len(skeleton["locals"])
    assert all(type(slot) is int and 0 <= slot < len(template["types"]) for slot in skeleton["locals"])
    return source, template


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

    def accepted(self, fixture, root="identity", crate_type="lib", abi_trace=False):
        environment = dict(self.environment)
        if abi_trace:
            environment["LEAN_MIRI_TRACE_ABI_CALLS"] = "1"
        result = self.export(fixture, root, environment=environment, crate_type=crate_type)
        self.last_abi_trace = result.stderr.splitlines()
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
                document = self.accepted(fixture, abi_trace=True)
                facts = document["compiler_function_facts"]
                llvm = [row for row in facts["types"]
                        if row["signature_query"]["abi"]["kind"] == "llvm_intrinsic"]
                self.assertTrue(llvm, "fixture must use the actual stdarch LLVM ABI")
                helpers = facts["helper_signatures"]
                self.assertFalse(any(row["signature"]["abi"]["kind"] == "llvm_intrinsic" for row in helpers))
                for row in llvm:
                    signature = row["signature_query"]
                    exact = [helper for helper in helpers
                             if helper["signature"]["abi"]["kind"] == "rust"
                             and helper["signature"]["inputs"] == signature["inputs"]
                             and helper["signature"]["output"] == signature["output"]]
                    if fixture == "llvm_source_abi":
                        self.assertEqual(signature["inputs"], [])
                        output = pool_entry(document, "types", signature["output"])
                        self.assertEqual(output["shape"], {"kind": "tuple", "elements": []})
                        self.assertEqual(exact, [], "covered empty Rust helper retained an ABI answer")
                        key = "signature=Binder { value: fn(), bound_vars: [] } extra=[]"
                        traces = [line for line in self.last_abi_trace
                                  if line.startswith("lean_miri_fn_pointer_abi_call ") and line.endswith(key)]
                        self.assertTrue(any("route=helper-source queried=false " in line for line in traces),
                                        "valid Rust helper constructor never reached source admission")
                        self.assertFalse(any("queried=true " in line for line in traces))
                        self.assertEqual(document["producer"]["abi_session"]["optimization"], "no")
                    else:
                        self.assertTrue(exact, "unsupported SIMD Rust helper lost its exact residual ABI")

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

    def test_foreign_repr_c_transfer_uses_raw_nominal_covariance(self):
        document = self.accepted("foreign_repr_c_transfer", crate_type="bin")
        types = {row['display']: row['type_id'] for row in document['types']}
        source, target = types['CallerType'], types['implementation::CalleeType']
        rows = [row for row in document['compiler_covariance_queries']
                if row['source_type'] == source and row['target_type'] == target]
        self.assertEqual(rows, [], "covered nominal relation retained an eager answer")
        source_shape, target_shape = document['types'][source]['shape'], document['types'][target]['shape']
        self.assertEqual(source_shape['kind'], 'adt')
        self.assertEqual(target_shape['kind'], 'adt')
        self.assertNotEqual(source_shape['def_id'], target_shape['def_id'],
                            "fixture lost its distinct nominal source identities")
        trace = self.export("foreign_repr_c_transfer", crate_type="bin",
                            environment=self.environment | {"LEAN_MIRI_TRACE_COVARIANCE_CALLS": "1"})
        self.assertEqual(trace.returncode, 0, trace.stderr)
        traced_types = {row['display']: row['type_id'] for row in load_mir_document(self.output)['types']}
        source, target = traced_types['CallerType'], traced_types['implementation::CalleeType']
        self.assertIn(f"queried=false source_id={source} target_id={target} ", trace.stderr)

    def test_shared_reborrow_uses_raw_nominal_covariance(self):
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
        self.assertTrue(reborrows, "fixture did not exercise shared Reborrow")
        for value in reborrows:
            source, target = value["place"]["type"], value["type"]
            self.assertNotEqual(source, target)
            rows = [row for row in document["compiler_covariance_queries"]
                    if row["source_type"] == source and row["target_type"] == target]
            self.assertEqual(rows, [], "covered reborrow retained an eager covariance answer")
            source_shape, target_shape = document['types'][source]['shape'], document['types'][target]['shape']
            self.assertEqual(source_shape['kind'], 'adt')
            self.assertEqual(target_shape['kind'], 'adt')
            self.assertNotEqual(source_shape['def_id'], target_shape['def_id'],
                                "same layout must not erase nominal identity")
        trace = self.export("shared_reborrow", environment=self.environment | {
            "LEAN_MIRI_TRACE_COVARIANCE_CALLS": "1"})
        self.assertEqual(trace.returncode, 0, trace.stderr)
        reborrows.clear()
        visit(load_mir_document(self.output)["bodies"])
        self.assertTrue(reborrows)
        for value in reborrows:
            source, target = value["place"]["type"], value["type"]
            self.assertIn(f"queried=false source_id={source} target_id={target} ", trace.stderr)

    def test_no_std_keeps_negative_and_optional_query_answers(self):
        document = self.accepted("no_std")
        self.assertNotIn("compiler_named_constants", document)
        self.assertNotIn("startup", document["compiler_runtime_queries"])
        unsigned = next(node for node in document["types"]
                        if node["shape"].get("unsigned_kind") == "u32")
        facts = unsigned["compiler_facts"]
        self.assertNotIn("is_dynamic", facts["boolean_queries"])
        self.assertNotIn("is_too_generic", facts["boolean_queries"])
        self.assertNotIn("boxed_type", facts["type_queries"])
        self.assertNotIn("builtin_deref_explicit", facts["type_queries"])
        self.assertNotIn("builtin_deref_implicit", facts["type_queries"])

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

    def test_result_main_has_exact_bootstrap_caller_signature(self):
        document = self.accepted("start_result", "main", "bin", abi_trace=True)
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
        expected = [main["signature_query"]["function_pointer_type"],
                    primitive["isize"], argv, primitive["u8"]]
        rows = document["compiler_function_facts"]["helper_signatures"]
        exact = [row for row in rows if row["signature"]["inputs"] == expected
                 and row["signature"]["output"] == primitive["isize"]
                 and row["signature"]["abi"]["kind"] == "rust"
                 and row["signature"]["safety"]["kind"] == "safe"
                 and not row["signature"]["c_variadic"]]
        self.assertTrue(exact, "nested dyn bootstrap helper lost its exact material ABI residual")
        self.assertTrue(all(isinstance(row["abi_query"], int) for row in exact))
        pointer = types[expected[0]]["shape"]
        self.assertEqual(pointer["kind"], "function_pointer")
        self.assertEqual(pointer["signature"]["inputs"], [])
        self.assertEqual(pointer["signature"]["abi"]["kind"], "rust")
        self.assertFalse(pointer["signature"]["c_variadic"])
        self.assertEqual(document["producer"]["abi_session"], {
            "panic": "unwind", "panic_in_drop": "unwind", "optimization": "no",
            "llvm_writable": False, "box_noalias": True,
            "incremental_enabled": False, "sanitizers": [],
        })
        traces = [line for line in self.last_abi_trace
                  if line.startswith("lean_miri_fn_pointer_abi_call ")
                  and "signature=Binder { value: fn(Binder { value: fn() -> " in line
                  and ", isize, *const *const u8, u8) -> isize, bound_vars: [] } extra=[]" in line]
        self.assertTrue(any("route=helper-residual queried=true " in line for line in traces),
                        "exact nested dyn bootstrap caller did not retain its physical ABI query")
        self.assertFalse(any("queried=false " in line for line in traces),
                         "nested dyn bootstrap was incorrectly admitted by the lossless-key provider")

    def test_weak_static_function_demands_retain_exact_named_queries(self):
        for fixture, name, args, ret in [
            ("weak_getrandom", "getrandom", ["pointer", "usize", "u32"], "isize"),
            ("weak_cxa", "__cxa_thread_atexit_impl", ["pointer"] * 3, "i32"),
        ]:
            with self.subTest(fixture=fixture):
                document = self.accepted(fixture)
                row = next(row for row in document["compiler_named_shim_abis"] if row["name"] == name)
                self.assertEqual(row["recipe"]["signature"]["arguments"], args)
                self.assertEqual(row["recipe"]["signature"]["return"], ret)
                self.assertIsInstance(row["recipe"]["query"]["abi_query"], int)

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
        images = [node for node in document["allocations"] if node["kind"] == "memory"]
        self.assertTrue(any(node["relocations"] for node in images))

    def test_required_foreign_tls_initializer_aborts_without_output(self):
        result = self.export("foreign_tls", "read_external")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("foreign thread-local initializer is unavailable", result.stderr)
        self.assertFalse(self.output.exists())

    def test_coroutine_metadata_retains_exact_coverage_and_runtime_abi(self):
        document = self.accepted("coroutine", "root")
        self.assertEqual(document["schema_version"], 13)
        coverage = document["compiler_coroutine_coverage"]
        self.assertTrue(coverage["coroutines"])
        self.assertEqual(len(coverage["body_coroutines"]), len(document["bodies"]))
        owners = {document["bodies"][row["owner_body"]]["instance_id"] for row in coverage["coroutines"]}
        self.assertTrue(owners <= {row["instance_id"] for row in document["compiler_instance_abis"]})
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

    def test_unknown_generic_runtime_constant_aborts_without_output(self):
        result = self.export("generic_runtime_constant", "root")
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.output.exists())
        self.assertIn("generic", result.stderr.lower())
        self.assertNotIn("panicked at", result.stderr)

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
        self.assertEqual(abi["calling_convention"], {"kind": "rust"})
        self.assertEqual((abi["arguments"], abi["fixed_count"], abi["c_variadic"]), ([], 0, False))
        self.assertEqual(abi["unwind_seed"], {
            "abi": {"kind": "rust", "unwind": None},
            "definition": {"never_unwind": False, "foreign_item": False, "drop_glue": False},
            "panic_unwinds": True, "panic_in_drop_unwinds": True})
        returned_layout = pool_entry(document, "layouts", abi["return"]["layout"])
        self.assertEqual(returned_layout["size_bytes"], 1)
        self.assertEqual(returned_layout["abi_align_bytes"], 1)
        self.assertEqual(returned_layout["backend_repr"], {"kind": "memory", "sized": True})
        self.assertFalse(returned_layout["uninhabited"])
        self.assertEqual(abi["return"]["mode"], {
            "kind": "Cast", "pad_i32_count": 0,
            "target": {"prefix_registers": [], "rest_offset_bytes": None,
                       "rest_register": {"kind": {"kind": "integer"}, "size_bits": 8},
                       "rest_total_bytes": 1, "rest_is_consecutive": False,
                       "attributes": {"regular_bits": 0, "arg_extension": {"kind": "none"},
                                      "pointee_size_bytes": 0, "pointee_align_bytes": None}}})
        if root["body_kind"] == "material":
            calls = [block["terminator"]["kind"] for block in root["basic_blocks"]
                     if block["terminator"]["kind"].get("variant") == "Call"]
            calls = [call for call in calls
                     if call["resolution"].get("instance_id") == instance["instance_id"]]
            self.assertTrue(calls, "fixture must call the concrete async constructor")
            self.assertTrue(all(call["resolution"]["fn_abi"] == queries[0]["abi_query"] for call in calls))
        else:
            _, template = raw_body_source(document, root)
            definition = pool_entry(document, "definitions", instance["def_id"])
            identity = {"crate": definition["crate"], "index": definition["index"]}
            calls = [block["terminator"]["kind"] for block in template["skeleton"]["blocks"]
                     if block["terminator"]["kind"].get("kind") == "source_call"]
            callees = [template["types"][call["function"]] for call in calls]
            matches = [callee for callee in callees if callee.get("tag") == "function_definition"
                       and callee["definition"] == identity]
            self.assertEqual(len(matches), 1, "raw root must call the exact async constructor")
            self.assertEqual(matches[0]["children"], [{"kind": "binder", "variables": [],
                "value": {"kind": "node", "sort": "aggregate", "tag": "arguments", "payload": "", "children": []}}])
            self.assertEqual(instance["generic_args"], [])

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
        self.assertNotIn("fixed_count", callee_abi)
        callee_seed = callee_abi["signature_seed"]
        callee_signature = callee_seed["signature"]
        self.assertEqual(callee_signature["abi"], {"kind": "c", "unwind": False})
        self.assertTrue(callee_signature["c_variadic"])
        self.assertEqual(callee_signature["inputs"], [extra["type_id"]])
        self.assertEqual(callee_seed["extra_argument_types"], rows[0]["extra_argument_types"])
        self.assertIsNone(callee_seed["caller_location"])
        self.assertEqual([argument["type"] for argument in callee_abi["arguments"]],
                         callee_signature["inputs"] + callee_seed["extra_argument_types"])
        caller_rows = [row for row in document["compiler_function_facts"]["pointer_abis"]
                       if row["extra_argument_types"] == rows[0]["extra_argument_types"]]
        caller_abis = [pool_entry(document, "fn_abis", row["abi_query"]) for row in caller_rows]
        mismatched_callers = [abi for abi in caller_abis
                              if abi.get("signature_seed", {}).get("signature", {}).get("inputs") == []]
        self.assertTrue(mismatched_callers,
                        "the actual caller/callee fixed-count mismatch must remain visible")
        for caller_abi in mismatched_callers:
            self.assertNotIn("fixed_count", caller_abi)
            caller_seed = caller_abi["signature_seed"]
            caller_signature = caller_seed["signature"]
            self.assertTrue(caller_abi["c_variadic"])
            self.assertTrue(caller_signature["c_variadic"])
            self.assertEqual(caller_signature["abi"], callee_signature["abi"])
            self.assertEqual(caller_seed["extra_argument_types"], callee_seed["extra_argument_types"])
            self.assertIsNone(caller_seed["caller_location"])
            self.assertEqual([argument["type"] for argument in caller_abi["arguments"]],
                             caller_seed["extra_argument_types"])
            self.assertEqual(caller_signature["output"], callee_signature["output"])
            self.assertEqual(caller_abi["calling_convention"], callee_abi["calling_convention"])
            # C signatures do not splat arguments. Their distinct raw input
            # counts reconstruct fixed_count=0 vs 1, despite identical extras.
            self.assertEqual(len(caller_signature["inputs"]), 0)
            self.assertEqual(len(callee_signature["inputs"]), 1)

    def test_resolved_generic_has_one_body_and_typed_constant_categories(self):
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
                if value.get("kind") in ("evaluated_const", "literal_const"):
                    self.assertEqual(set(value), {"kind", "value"})
                elif value.get("kind") == "type_constant":
                    self.assertEqual(set(value), {"kind", "type_constant"})
                    self.assertIs(type(value["type_constant"]), int)
                    source = pool_entry(document, "type_constants", value["type_constant"])
                    self.assertEqual(source["kind"], "value")
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
        material_count = source_count = 0
        for body in document["bodies"]:
            self.assertFalse(removed & body.keys())
            if body["body_kind"] == "material":
                material_count += 1
                self.assertIn("required_consts", body)
                self.assertIsInstance(body["required_consts"], list)
                locals_, scopes = body["locals"], body["source_scopes"]
            else:
                source_count += 1
                source, template = raw_body_source(document, body)
                # Raw copy templates admit only an explicit empty required-const
                # preamble (generic_mir::capture_mode); they do not serialize a
                # closed-body field. Keep checking that category on material MIR.
                self.assertNotIn("required_consts", body)
                self.assertNotIn("required_consts", template["skeleton"])
                self.assertFalse((removed - {"source_promoted"}) & source.keys())
                locals_, scopes = source["local_sources"], source["source_scopes"]
            for local in locals_:
                self.assertFalse({"local_info", "mutability", "layout"} & local.keys())
            for scope in scopes:
                self.assertNotIn("local_data", scope)
        self.assertGreater(material_count, 0, "required-constant material category must remain exercised")
        self.assertGreater(source_count, 0, "raw source metadata category must be exercised")

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
