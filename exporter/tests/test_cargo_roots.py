import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_inspection_document


class CargoRootTests(unittest.TestCase):
    def test_selected_library_roots_reach_external_instances_and_shims(self):
        exporter = Path(os.environ.get("EXPORTER_BIN", ROOT / "exporter/target/debug/lean-miri-mir-exporter")).resolve()
        toolchain = Path(os.environ.get("RUSTUP_HOME", ROOT / ".rustup")) / "toolchains/miri-exporter-8eb778d04094"
        environment = dict(os.environ)
        environment["PATH"] = f"{toolchain / 'bin'}:{os.environ['PATH']}"
        environment["LD_LIBRARY_PATH"] = f"{toolchain / 'lib'}:{os.environ.get('LD_LIBRARY_PATH', '')}"
        environment["MIRI_SYSROOT"] = os.environ.get("MIRI_SYSROOT", str(ROOT / "scratch/lake/miri-sysroot"))
        environment["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "0"
        environment["LEAN_MIRI_RUN_PREPARED_MIRI"] = "0"
        cases = [
            ("cargo-external", "exporter-cargo-app", ["external_generic_call"]),
            ("cargo-instance-mir", "ctfe-consumer", ["make_pair", "make_token", "constants", "call_once_shim", "invoke"]),
        ]
        with tempfile.TemporaryDirectory(prefix="lean-miri-cargo-roots-") as temporary:
            for fixture, package, roots in cases:
                with self.subTest(fixture=fixture):
                    target = Path(temporary) / fixture
                    environment["CARGO_TARGET_DIR"] = str(target)
                    command = [str(exporter), "--cargo"]
                    for root in roots:
                        command += ["--root", root]
                    command += ["check", "--lib", "--offline", "--locked", "-p", package,
                                "--manifest-path", str(ROOT / "exporter/fixtures" / fixture / "Cargo.toml")]
                    result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, text=True)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    outputs = list(target.rglob("lean-miri-mir/*.json"))
                    self.assertEqual(len(outputs), 1, "dependencies must build with MIR without becoming exporter roots")
                    document = load_mir_inspection_document(outputs[0])
                    self.assertEqual({root["def_path"] for root in document["selected_scope"]["roots"]}, set(roots))
                    self.assertEqual(document["invocation"]["root_paths"], roots)
                    executable = [row for row in document["instances"] if row["kind"] == "instance_mir"]
                    if fixture == "cargo-external":
                        paths = {row["def_path"] for row in executable}
                        self.assertEqual(paths, {"external_generic_call", "exporter_helper::wrap", "exporter_helper::identity"})
                        for instance in executable:
                            if instance["def_path"].startswith("exporter_helper::"):
                                self.assertEqual(len(instance["generic_args"]), 1)
                                self.assertEqual(instance["generic_args"][0]["kind"], "type")
                        switched = command[:]
                        switched[switched.index("external_generic_call")] = "external_std_call"
                        result = subprocess.run(switched, cwd=ROOT, env=environment, capture_output=True, text=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        exports = [load_mir_inspection_document(path) for path in target.rglob("lean-miri-mir/*.json")]
                        self.assertEqual({tuple(row["invocation"]["root_paths"]) for row in exports},
                                         {("external_generic_call",), ("external_std_call",)})
                        result = subprocess.run(command, cwd=ROOT, env=environment, capture_output=True, text=True)
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertEqual(len(list(target.rglob("lean-miri-mir/*.json"))), 3,
                                         "repeating identical roots must export afresh")
                    else:
                        self.assertTrue(any(row["def_path"].startswith("ctfe_producer_types::Pair") for row in executable))
                        self.assertTrue(any(row["def_path"].startswith("ctfe_producer_types::Token") for row in executable))
                        self.assertTrue(any(row["instance_kind"].get("shim_kind") == "closure_once" for row in executable))
                        self.assertEqual([row["def_path"] for row in document["root_declarations"]], ["invoke"])
                        self.assertNotIn("invoke", {row["def_path"] for row in document["body_roots"]})
                        constants = next(row for row in executable if row["def_path"] == "constants")
                        body = document["bodies"][constants["body"]]
                        bits = []
                        def collect(value):
                            if isinstance(value, dict):
                                if "bits_unsigned" in value:
                                    bits.append(value["bits_unsigned"])
                                for child in value.values():
                                    collect(child)
                            elif isinstance(value, list):
                                for child in value:
                                    collect(child)
                        collect(body)
                        self.assertTrue({"42", "121"}.issubset(bits))


if __name__ == "__main__":
    unittest.main()
