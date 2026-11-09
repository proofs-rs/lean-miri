#!/usr/bin/env python3
"""Exercise metadata operations on fresh pinned compiler query results."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document

env = dict(os.environ)
elan = Path(env.setdefault("ELAN_HOME", str(ROOT / ".elan")))
rustup = Path(env.setdefault("RUSTUP_HOME", str(ROOT / ".rustup")))
env.setdefault("CARGO_HOME", str(ROOT / ".cargo"))
env.setdefault("MIRI_SYSROOT", str(ROOT / "scratch/miri-sysroot"))
toolchain = rustup / "toolchains/miri-exporter-8144389c895d"
env["PATH"] = str(toolchain / "bin") + ":" + env.get("PATH", "")
env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + (":" + env["LD_LIBRARY_PATH"] if env.get("LD_LIBRARY_PATH") else "")
exporter = env.get("EXPORTER_BIN", str(ROOT / "exporter/target/debug/lean-miri-mir-exporter"))
lock = json.loads((ROOT / "upstream/source-lock.json").read_text())

with tempfile.TemporaryDirectory(prefix="runtime-metadata-") as directory:
    for source, root, module in [
        ("fixture.rs", "records", "RuntimeMetadata"),
        ("str_field.rs", "str_field", "StrFieldProjection"),
    ]:
        output = Path(directory) / f"{root}.json"
        subprocess.run([exporter, "--output", str(output), "--root", root,
                        str(ROOT / "tests/runtime_metadata" / source), "--crate-type=lib",
                        f"--crate-name=runtime_metadata_{root}"], cwd=ROOT, env=env, check=True)
        document = load_mir_document(output)
        assert document["producer"]["rustc_commit"] == lock["pins"]["rustc"]["commit"]
        assert document["producer"]["miri_commit"] == lock["pins"]["miri"]["commit"]
        subprocess.run([str(elan / "bin/lake"), "env", "lean", "--run",
                        f"tests/runtime_metadata/{module}.lean", str(output)],
                       cwd=ROOT, env=env, check=True)
