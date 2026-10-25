#!/usr/bin/env python3
"""Exhaust the SC/Relaxed two-location projection against pinned Miri fetch_store.

The Miri candidate selector below is extracted verbatim from the pinned Rust
method except for (1) removing its RNG parameter/import and (2) replacing the
random `choose` tail with a collection of all supported candidates. A small
Python driver applies the pinned vector-clock, atomic-load/store, and thread
creation rules to the four-event projection and asks that compiled Rust method
for candidates at each reachable load state. This is a source-derived bounded
reference model, not an execution of the Miri interpreter.
"""

from __future__ import annotations

from collections import Counter
from copy import deepcopy
import hashlib
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
RULES = json.loads((ROOT / "tests/connected/fixtures/selector-rules.json").read_text())
WEAK_PATH = "upstream/miri-source/src/concurrency/weak_memory.rs"
RACE_PATH = "upstream/miri-source/src/concurrency/data_race.rs"
PINS = {item["path"]: item["sha256"] for item in RULES["sources"]}

ORDERS = [
    ("AS", "AL", "BS", "BL"),
    ("AS", "BS", "AL", "BL"),
    ("AS", "BS", "BL", "AL"),
    ("BS", "AS", "AL", "BL"),
    ("BS", "AS", "BL", "AL"),
    ("BS", "BL", "AS", "AL"),
]


def require_pinned_source(path: str) -> str:
    data = (ROOT / path).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    wanted = PINS.get(path)
    if wanted is None or actual != wanted:
        raise SystemExit(f"pinned source mismatch for {path}: expected {wanted}, got {actual}")
    return data.decode()


def extract_fetch_store(source: str) -> str:
    marker = "    fn fetch_store<R: rand::Rng + ?Sized>("
    start = source.index(marker)
    open_brace = source.index("{", start)
    depth = 1
    end = open_brace + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    body = source[open_brace + 1 : end - 1]
    body = body.replace("        use rand::seq::IteratorRandom;\n", "")
    choose = "        let chosen = candidates.choose(rng).expect(\"store buffer cannot be empty\");"
    cut = body.index(choose)
    body = body[:cut] + """        candidates.map(|chosen| {
            let position = self.buffer.iter().position(|item| std::ptr::eq(item, chosen)).unwrap();
            (position, chosen.val.unwrap())
        }).collect()
"""
    return "fn fetch_candidates(&self, is_seqcst: bool, clocks: &ThreadClockSet) -> Vec<(usize, u8)> {" + body + "}"


RUST_TEMPLATE = r'''use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::io::{self, BufRead};
use std::ops::Index;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)] struct VectorIdx(usize);
#[derive(Clone, Debug)] struct VClock(Vec<u64>);
static ZERO: u64 = 0;
impl Index<VectorIdx> for VClock {
    type Output = u64;
    fn index(&self, i: VectorIdx) -> &u64 { self.0.get(i.0).unwrap_or(&ZERO) }
}
#[derive(Clone)] struct ThreadClockSet { clock: VClock, write_seqcst: VClock, read_seqcst: VClock }
#[derive(Default)] struct LoadInfo { timestamps: HashMap<VectorIdx, u64>, sc_loaded: bool }
struct StoreElement { store_thread: VectorIdx, store_timestamp: u64, is_seqcst: bool,
                     load_info: RefCell<LoadInfo>, val: Option<u8> }
struct StoreBuffer { buffer: VecDeque<StoreElement> }
#[derive(PartialEq)] enum LoadRecency { Latest, Outdated }

impl StoreBuffer {
FETCH_METHOD
}

fn vec_clock(text: &str) -> VClock {
    VClock(text.split(',').map(|v| v.parse::<u64>().unwrap()).collect())
}
fn main() {
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let fields: Vec<_> = line.split('|').collect();
        let is_sc = fields[0] == "1";
        let clocks = ThreadClockSet { clock: vec_clock(fields[1]),
            write_seqcst: vec_clock(fields[2]), read_seqcst: vec_clock(fields[3]) };
        let mut buffer = VecDeque::new();
        for encoded in fields[4].split(';') {
            let v: Vec<_> = encoded.split(',').collect();
            let thread = VectorIdx(v[0].parse().unwrap());
            let mut info = LoadInfo { timestamps: HashMap::new(), sc_loaded: v[3] == "1" };
            for i in 0..3 {
                if v[4+i] != "-" { info.timestamps.insert(VectorIdx(i), v[4+i].parse().unwrap()); }
            }
            buffer.push_back(StoreElement { store_thread: thread,
                store_timestamp: v[1].parse().unwrap(), is_seqcst: v[2] == "1",
                load_info: RefCell::new(info), val: Some(v[7].parse().unwrap()) });
        }
        let found = StoreBuffer { buffer }.fetch_candidates(is_sc, &clocks);
        println!("{}", found.iter().map(|(p,v)| format!("{p}:{v}")).collect::<Vec<_>>().join(";"));
    }
}
'''


def build_rust_oracle(fetch_method: str, source_directory: Path, binary_directory: Path) -> Path:
    rustc = shutil.which("rustc")
    if rustc is None:
        candidate = ROOT / ".rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc"
        rustc = str(candidate) if candidate.is_file() else None
    if rustc is None:
        raise SystemExit("rustc is unavailable for source-extracted selector oracle")
    source = RUST_TEMPLATE.replace("FETCH_METHOD", fetch_method)
    rs_path = source_directory / "miri_fetch_store_candidates.rs"
    exe_path = binary_directory / "miri_fetch_store_candidates"
    rs_path.write_text(source)
    command = [rustc, "--edition=2024", "-Awarnings", str(rs_path), "-o", str(exe_path)]
    proc = subprocess.run(command,
                          text=True, capture_output=True)
    build_record = {
        "command": command,
        "cwd": str(ROOT),
        "rustc_sha256": hashlib.sha256(Path(rustc).read_bytes()).hexdigest(),
        "source_sha256": hashlib.sha256(rs_path.read_bytes()).hexdigest(),
        "exit_code": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }
    (source_directory / "rustc-build.json").write_text(json.dumps(build_record, indent=2) + "\n")
    if proc.returncode:
        raise SystemExit(f"could not compile extracted Miri selector:\n{proc.stdout}{proc.stderr}")
    return exe_path


def join(left: list[int], right: list[int]) -> list[int]:
    return [max(a, b) for a, b in zip(left, right)]


def inc(clock: list[int], index: int) -> list[int]:
    result = clock.copy()
    result[index] += 1
    return result


def initial_state(sc: bool) -> dict:
    # `GlobalState.threadCreated` for A and then B: each child joins the
    # current main clock; parent and child coordinates are then incremented.
    main = [0, 0, 0]
    a = [0, 0, 0]
    a = join(a, main)
    main = inc(main, 0)
    a = inc(a, 1)
    b = [0, 0, 0]
    b = join(b, main)
    main = inc(main, 0)
    b = inc(b, 2)
    return {
        "sc": sc,
        "clocks": [main, a, b],
        "read_sc": [[0, 0, 0] for _ in range(3)],
        "write_sc": [[0, 0, 0] for _ in range(3)],
        "last_sc_write": [0, 0, 0],
        "locs": {
            "X": {"entries": None, "sync": [0, 0, 0], "latest": 0},
            "Y": {"entries": None, "sync": [0, 0, 0], "latest": 0},
        },
        "reads": {"A": None, "B": None},
    }


def encode_query(sc: bool, clock: list[int], read_sc: list[int], write_sc: list[int], entries: list[dict]) -> str:
    encoded_entries = []
    for entry in entries:
        info = [entry["loads"].get(i) for i in range(3)]
        encoded_entries.append(",".join([
            str(entry["thread"]), str(entry["timestamp"]), str(int(entry["sc"])),
            str(int(entry["sc_loaded"])), *("-" if n is None else str(n) for n in info), str(entry["value"]),
        ]))
    return "|".join([
        str(int(sc)), ",".join(map(str, clock)), ",".join(map(str, write_sc)),
        ",".join(map(str, read_sc)), ";".join(encoded_entries),
    ])


def run_selector(exe: Path, query: str) -> list[tuple[int, int]]:
    proc = subprocess.run([str(exe)], input=query + "\n", text=True, capture_output=True)
    if proc.returncode:
        raise SystemExit(f"extracted Miri candidate selector failed: {proc.stderr}")
    line = proc.stdout.strip()
    if not line:
        return []
    return [tuple(map(int, item.split(":"))) for item in line.split(";")]


def miri_candidates(state: dict, thread: int, location: str, exe: Path) -> list[tuple[int, int]]:
    loc = state["locs"][location]
    if loc["entries"] is None:
        return []
    query = encode_query(state["sc"], state["clocks"][thread], state["read_sc"][thread],
                         state["write_sc"][thread], loc["entries"])
    candidates = run_selector(exe, query)
    if not candidates:
        raise SystemExit("pinned Miri fetch_store produced an empty candidate set")
    return candidates


def execute_one(state: dict, event: str, exe: Path) -> list[dict]:
    next_state = deepcopy(state)
    sc = state["sc"]
    if event in ("AS", "BS"):
        thread = 1 if event == "AS" else 2
        location = "X" if event == "AS" else "Y"
        loc = next_state["locs"][location]
        before = next_state["clocks"][thread].copy()
        # SeqCst/Release atomic-store validation publishes the pre-increment
        # release clock, then maybe_perform_sync_operation increments once.
        loc["sync"] = before.copy()
        after = inc(before, thread)
        next_state["clocks"][thread] = after
        if sc:
            next_state["last_sc_write"][thread] = after[thread]
        if loc["entries"] is None:
            loc["entries"] = [{"thread": 0, "timestamp": 0, "sync": [0, 0, 0],
                               "sc": False, "sc_loaded": False, "loads": {}, "value": 0}]
        loc["entries"].append({"thread": thread, "timestamp": after[thread], "sync": loc["sync"].copy(),
                               "sc": sc, "sc_loaded": False, "loads": {}, "value": 1})
        if sc:
            # Exact store_impl marking predicate from pinned weak_memory.rs.
            for entry in loc["entries"]:
                happens_before = entry["timestamp"] <= after[entry["thread"]]
                coherence_before = any(ts <= after[load_thread]
                                       for load_thread, ts in entry["loads"].items())
                if happens_before or coherence_before:
                    entry["sc"] = True
        loc["latest"] = 1
        return [next_state]

    thread = 1 if event == "AL" else 2
    location = "Y" if event == "AL" else "X"
    loc = next_state["locs"][location]
    if sc:
        # `last_sc_fence` is zero in this fence-free fixture.
        next_state["read_sc"][thread] = join(next_state["read_sc"][thread], [0, 0, 0])
    candidates = miri_candidates(state, thread, location, exe)
    if not candidates:
        # The source fallback validates with no selected-store override.
        choices = [(-1, loc["latest"])]
    else:
        choices = candidates

    results = []
    for position, value in choices:
        branch = deepcopy(next_state)
        clocks = branch["clocks"][thread]
        selected_sync = [0, 0, 0] if position == -1 else loc["entries"][position]["sync"]
        if sc:
            clocks = join(clocks, selected_sync)
        else:
            # Relaxed loads accumulate an acquire-fence clock; this fixture has
            # no later fence, but preserve the state transition shape.
            pass
        clocks = inc(clocks, thread)
        branch["clocks"][thread] = clocks
        if position != -1:
            entry = branch["locs"][location]["entries"][position]
            entry["loads"].setdefault(thread, clocks[thread])
            entry["sc_loaded"] = entry["sc_loaded"] or sc
        branch["reads"]["A" if event == "AL" else "B"] = value
        results.append(branch)
    return results


def execute_schedule(sc: bool, schedule: tuple[str, ...], exe: Path) -> list[tuple[int, int]]:
    states = [initial_state(sc)]
    for event in schedule:
        states = [child for state in states for child in execute_one(state, event, exe)]
    return [(state["reads"]["A"], state["reads"]["B"]) for state in states]


def lean_outcomes(sc: bool, lean_source: Path) -> list[tuple[int, int]]:
    lake = ROOT / ".elan/bin/lake"
    proc = subprocess.run([str(lake), "env", "lean", "--run",
                           str(lean_source)],
                          cwd=ROOT, env={**os.environ, "ELAN_HOME": str(ROOT / ".elan")},
                          text=True, capture_output=True)
    if proc.returncode:
        raise SystemExit(f"Lean projection failed:\n{proc.stdout}{proc.stderr}")
    prefix = "projection202:sc:" if sc else "projection202:relaxed:"
    line = next((line for line in proc.stdout.splitlines() if line.startswith(prefix)), None)
    if line is None:
        raise SystemExit(f"missing Lean projection output {prefix!r}:\n{proc.stdout}")
    payload = line[len(prefix):]
    if payload.startswith("error:"):
        raise SystemExit(f"Lean projection returned failure: {payload}")
    if not payload:
        return []
    return [tuple(map(int, pair.split(","))) for pair in payload.split(";")]


def run_reference(source_directory: Path, binary_directory: Path, lean_source: Path) -> None:
    weak = require_pinned_source(WEAK_PATH)
    require_pinned_source(RACE_PATH)
    fetch_method = extract_fetch_store(weak)
    exe = build_rust_oracle(fetch_method, source_directory, binary_directory)
    for sc, label in ((True, "SeqCst"), (False, "Relaxed")):
        reference = [pair for schedule in ORDERS for pair in execute_schedule(sc, schedule, exe)]
        lean = lean_outcomes(sc, lean_source)
        if Counter(reference) != Counter(lean):
            raise SystemExit(f"{label} projected outcome multiset differs: Lean={lean}; Miri-reference={reference}")
        if sc and (0, 0) in reference:
            raise SystemExit("forbidden (0,0) unexpectedly appears in projected SeqCst relation")
        if not sc and (0, 0) not in reference:
            raise SystemExit("Relaxed projection did not contain the expected (0,0) witness")
        print(f"projection202:{label}:orders={len(ORDERS)}:ranked_outcomes={len(reference)}:pairs={sorted(set(reference))}")
    print("projection202:source-extracted-fetch-store:sha-locked:Rust RNG tail replaced by full candidate collection")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--capture-dir", type=Path,
                        help="keep the extracted Rust selector source and build record here")
    parser.add_argument("--binary-dir", type=Path,
                        help="keep the generated selector executable outside the source evidence directory")
    parser.add_argument("--lean-source", type=Path,
                        default=ROOT / "tests/connected/proofs/ScProjection202.lean",
                        help="Lean projection source to compare against (prefer the attempt-local copy)")
    args = parser.parse_args()
    if args.capture_dir is not None:
        if args.binary_dir is None:
            raise SystemExit("--binary-dir is required with --capture-dir")
        args.capture_dir.mkdir(parents=True, exist_ok=False)
        args.binary_dir.mkdir(parents=True, exist_ok=False)
        run_reference(args.capture_dir, args.binary_dir, args.lean_source.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="sc-projection202-") as tmp:
            directory = Path(tmp)
            run_reference(directory, directory, args.lean_source.resolve())


if __name__ == "__main__":
    main()
