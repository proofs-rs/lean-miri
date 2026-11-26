#!/usr/bin/env python3
"""Check historical fixture bytes and freshly export current regression inputs."""
import argparse
import gzip
import hashlib
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = {
    "u32": ("source133-root-u32-001", "1ef4f7fc734799b89e984a42f93ae2357f88f50a57a495af6cd8076f42b777d6", "root_u32", "lib", "2021"),
    "control-flow": ("source133-root-control-flow-001", "2b5c83a8c9ecfb7de63c61377cf78aa057a599846672521b8bc8ff04b423c175", "root_control_flow", "lib", "2021"),
    "nostd-startup": ("source133-nostd-startup-001", "aac87e10ad03b3e75d8c62e2e3d81a9c48ef6615020354c40cc121d6d3f10cae", "miri_start", "bin", "2024"),
}

ARCHIVE_SHA256 = {
    "u32": "a427ae125a33563aae9235041f0315e5d5b3dab0d7bf78165212ce8386eea43d",
    "control-flow": "fcf63af6751290127a7ebbb8f8dcda8d254f2692ba51832a97ebf33e6093da42",
    "nostd-startup": "208dc49f71531b8d519d273df8866422dd281b6488351d91252558ad583e9ce9",
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "scratch/regression-inputs")
    parser.add_argument("--fixture", action="append", choices=FIXTURES)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ)
    rustup = Path(environment.get("RUSTUP_HOME", ROOT / ".rustup"))
    toolchain = rustup / "toolchains/miri-exporter-8eb778d04094"
    environment["PATH"] = str(toolchain / "bin") + ":" + environment["PATH"]
    environment["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + environment.get("LD_LIBRARY_PATH", "")
    environment["MIRI_SYSROOT"] = environment.get("MIRI_SYSROOT", str(ROOT / "scratch/lake/miri-sysroot"))
    environment["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    environment["LEAN_MIRI_RUN_PREPARED_MIRI"] = "0"
    exporter = environment.get("EXPORTER_BIN", str(ROOT / "exporter/target/debug/lean-miri-mir-exporter"))
    for name in args.fixture or FIXTURES:
        archive, digest, root, crate_type, edition = FIXTURES[name]
        # Historical bytes remain evidence of the earlier producer. They are
        # checked independently and never fed to the current input decoder.
        compressed = (ROOT / "tests/eval_core/fixtures" / f"{archive}.json.gz").read_bytes()
        if hashlib.sha256(compressed).hexdigest() != ARCHIVE_SHA256[name]:
            raise SystemExit(f"{archive}: historical archive hash mismatch")
        raw = gzip.decompress(compressed)
        if hashlib.sha256(raw).hexdigest() != digest:
            raise SystemExit(f"{archive}: historical input hash mismatch")
        stem = {"u32": "root_u32", "control-flow": "root_control_flow", "nostd-startup": "nostd_startup"}[name]
        source = ROOT / "tests/eval_core/fixtures" / f"{stem}.rs"
        output = args.output / f"{name}.json"
        subprocess.run([exporter, "--output", str(output), "--root", root, "--", str(source),
                        f"--crate-type={crate_type}", f"--crate-name={'source133_nostd_startup' if name == 'nostd-startup' else stem}", f"--edition={edition}",
                        "-Cpanic=abort", "-Zmir-opt-level=0"], cwd=ROOT, env=environment, check=True)
        subprocess.run([sys.executable, str(ROOT / "tests/eval_core/copy_fixture.py"),
                        str(output), str(args.output / f"{name}.checked.json")], check=True)


if __name__ == "__main__":
    main()
