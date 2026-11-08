#!/usr/bin/env python3
"""Alternate immutable exporter binaries on one source, recording process resources.

Run with the pinned toolchain on PATH and MIRI_SYSROOT/LD_LIBRARY_PATH set.
Trial zero warms both binaries; all raw trials, CPU steal and cgroup counters
are retained. This measures compiler/export only, not Lean guest execution.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def counters(cpu):
    lines = Path("/proc/stat").read_text().splitlines()
    return {
        "proc_stat_cpu": lines[0],
        "proc_stat_selected_cpu": next(line for line in lines if line.startswith(f"cpu{cpu} ")),
        "cgroup_cpu_stat": Path("/sys/fs/cgroup/cpu.stat").read_text(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, type=Path)
    parser.add_argument("--candidate", required=True, type=Path)
    parser.add_argument("--source", type=Path)
    parser.add_argument("--body-stress", action="store_true")
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--cpu", type=int, default=2)
    parser.add_argument("--trials", type=int, default=4)
    parser.add_argument("--root", action="append", default=[])
    args = parser.parse_args()
    if bool(args.source) == args.body_stress or args.trials < 1:
        parser.error("choose one of --source/--body-stress and at least one measured trial")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source = args.source
    if args.body_stress:
        source = args.output_dir / "duplicated-bodies.rs"
        source.write_text("#![no_std]\n" + "\n".join(
            "pub fn f%d(mut x:u64)->u64 { %s x }" %
            (i, " ".join("x=x.wrapping_add(%d);" % j for j in range(24)))
            for i in range(300)))
    binaries = {"baseline": args.baseline.resolve(), "candidate": args.candidate.resolve()}
    hashes = {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in binaries.items()}
    report = {"cpu": args.cpu, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
              "binary_sha256": hashes, "rows": []}
    for trial in range(args.trials + 1):
        order = list(binaries) if trial % 2 == 0 else list(reversed(binaries))
        for name in order:
            output = args.output_dir / (name + ".json")
            command = [str(binaries[name]), "--output", str(output)]
            for root in args.root:
                command += ["--root", root]
            command += ["--", str(source), "--crate-name", "online_compare", "--crate-type", "lib",
                        "--edition=2021", "--cfg", "miri", "-Zalways-encode-mir", "-Zmir-opt-level=0",
                        "-Cpanic=abort", "--sysroot", os.environ["MIRI_SYSROOT"]]
            before, start = counters(args.cpu), time.monotonic()
            with (args.output_dir / f"{name}-{trial}.log").open("w") as log:
                process = subprocess.Popen(command, stdout=log, stderr=log,
                    preexec_fn=lambda: os.sched_setaffinity(0, {args.cpu}))
                _, status, usage = os.wait4(process.pid, 0)
                process.returncode = os.waitstatus_to_exitcode(status)
            row = {"trial": trial, "warmup": trial == 0, "binary": name,
                   "wall_s": time.monotonic() - start, "user_s": usage.ru_utime,
                   "system_s": usage.ru_stime, "maxrss_kib": usage.ru_maxrss,
                   "exit": process.returncode, "before": before, "after": counters(args.cpu), "command": command,
                   "output_bytes": output.stat().st_size if process.returncode == 0 else None}
            report["rows"].append(row)
            (args.output_dir / "resources.json").write_text(json.dumps(report, indent=2) + "\n")
            print({key: value for key, value in row.items() if key not in ("before", "after")}, flush=True)
            if process.returncode:
                raise SystemExit(process.returncode)
    if any(hashlib.sha256(path.read_bytes()).hexdigest() != hashes[name] for name, path in binaries.items()):
        raise SystemExit("exporter artifact changed during measurement")


if __name__ == "__main__":
    main()
