#!/usr/bin/env python3
"""Independently validate one canonical seeded replay's SC event order.

Usage: validate_orders.py SNAPSHOT RUN_LOG OUTPUT_JSON

The replay is expected to come from the verification-only SC264 trace wrapper,
run against the unchanged schema-3 198-sc-base snapshot. This checker reads
only those artifacts; it never executes Lean or changes a guest input.
"""
import hashlib
import json
import struct
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from mir_json import load_mir_document


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


BASE198_SHA256 = "4d706432e0423d3acf43e6f54b8b9cf1151c1a0e2ae9f203e88267fd6d94a8ec"

STEP = re.compile(
    r"sc264_core_step thread=\{ value := (\d+) \}; choice_cursor=(\d+); "
    r"frame=some \(\{ kind := Miri\.Interpreter\.CallInstanceKind\.Item "
    r"(\d+),\s*args := #\[(?:.*?)\] \},\s*"
    r"Miri\.Interpreter\.FrameLocation\.mir \{ block := (\d+), "
    r"statementIndex := (\d+)", re.S
)
STEP_START = re.compile(
    r"sc264_core_step thread=\{ value := (\d+) \}; choice_cursor=(\d+); frame="
)
STEP_END = re.compile(r"sc264_core_step_end choice_cursor=(\d+)")

EVENT_CHUNK = re.compile(r"\{ request :=", re.S)
REQUEST = re.compile(
    r"Request\.(index|bernoulli)\s*\(Miri\.Interpreter\.ExecutionChoices\."
    r"(IndexSite|BoolSite)\.(\w+)\)\s*(\d+)"
)
INPUT = re.compile(
    r"Input\.(index|boolean)\s*\(Miri\.Interpreter\.ExecutionChoices\."
    r"(IndexSite|BoolSite)\.(\w+)\)\s*(\d+|true|false)"
)


def parse_events(log, terminal_cursor):
    need(log.count("choice_events=#") == 1,
         "run log must contain exactly one terminal choice event trace")
    tail = log.split("choice_events=#[", 1)[1]
    chunks = EVENT_CHUNK.split(tail)[1:]
    events = []
    for i, chunk in enumerate(chunks):
        if "]" in chunk:
            chunk = chunk.split("]", 1)[0]
        request = REQUEST.search(chunk)
        value = INPUT.search(chunk)
        need(request is not None and value is not None,
             f"choice event {i} is incomplete or malformed")
        request_kind, request_site_kind, request_site, support_text = request.groups()
        input_kind, input_site_kind, input_site, value_text = value.groups()
        need(request_site_kind == input_site_kind and request_site == input_site,
             f"choice event {i} request/input site mismatch")
        support = int(support_text)
        if input_kind == "index":
            need(request_kind == "index", f"choice event {i} has a non-index request")
            selected = int(value_text)
            need(support > 0 and 0 <= selected < support,
                 f"choice event {i} selected {selected} outside support {support}")
        else:
            need(request_kind == "bernoulli" and value_text in ("true", "false"),
                 f"choice event {i} has an invalid Boolean request/input")
            selected = value_text == "true"
            rate = struct.unpack("<d", struct.pack("<Q", support))[0]
            need(0.0 <= rate <= 1.0, f"choice event {i} has invalid Bernoulli rate {rate}")
            numerator, denominator = rate.as_integer_ratio()
            threshold = numerator * (1 << 64) // denominator
            need((not selected and threshold < (1 << 64)) or (selected and threshold > 0),
                 f"choice event {i} selected Boolean outside Bernoulli support")
        events.append({
            "request": {"kind": request_kind, "site": request_site, "support": support},
            "input": {"kind": input_kind, "site": input_site, "value": selected},
        })
    need(len(events) == terminal_cursor,
         f"parsed {len(events)} choice events, terminal cursor reports {terminal_cursor}")
    return events


def source_sites(snapshot):
    document = load_mir_document(snapshot)
    bodies = []

    def add_body(body, name):
        bodies.append((body, name))
        for promoted in body.get("promoted_bodies", []) or []:
            if promoted.get("body") is not None:
                add_body(promoted["body"], name + "::promoted")

    for body in document["bodies"]:
        add_body(body, body.get("def_path", "root"))
    for instance in document["instances"]:
        if instance.get("body") is not None:
            add_body(instance["body"], instance["def_path"])

    definitions = []

    def identity(body):
        return body.get("def_id", body.get("source_def_id"))

    for body, _ in bodies:
        definition = identity(body)
        if definition is not None and definition not in definitions:
            definitions.append(definition)
    for instance in document["instances"]:
        definition = instance.get("def_id")
        if definition is not None and definition not in definitions:
            definitions.append(definition)

    intrinsic_sites = {}
    workers = {}
    worker_frames = {}
    for body, name in bodies:
        dense = definitions.index(identity(body))
        if name in ("child_a", "child_b"):
            workers[name] = dense
            worker_frames[dense] = name
        for block in body["basic_blocks"]:
            terminator = block["terminator"]["kind"]
            if terminator.get("variant") != "Call":
                continue
            callee = terminator.get("resolution", {}).get("instance_def_path")
            if not callee:
                continue
            if name.startswith("core::sync::atomic::atomic_store") and callee.endswith("core::intrinsics::atomic_store"):
                intrinsic_sites[(dense, block["block"], len(block["statements"]))] = "store"
            elif name.startswith("core::sync::atomic::atomic_load") and callee.endswith("core::intrinsics::atomic_load"):
                intrinsic_sites[(dense, block["block"], len(block["statements"]))] = "load"
    need(set(workers) == {"child_a", "child_b"},
         f"snapshot worker definitions differ: {workers}")
    need(intrinsic_sites, "snapshot exposes no atomic intrinsic wrapper call sites")
    return intrinsic_sites, workers, worker_frames


def check(snapshot, run_log):
    snapshot, run_log = Path(snapshot), Path(run_log)
    need(sha(snapshot) == BASE198_SHA256,
         "snapshot is not the pinned unchanged 198-sc-base export")
    text = run_log.read_text()
    need(text.count("sc_ordering_control_fixture=PASS") == 1,
         "run log must contain exactly one successful terminal record")
    need("sc_ordering_control_fixture=PASS" in text,
         "canonical SC fixture did not report PASS")
    seed_match = re.search(
        r"choice_mode=bounded-seeded-diagnostic seed=(\d+) algorithm=SplitMix64-v1; "
        r"outcome=exit_zero; leak_check=true; threads=3; choice_cursor=(\d+); "
        r"atomic_stale_supports=\#\[[^\]]*\]; active_frame=none; choice_events=\#\[", text)
    need(seed_match is not None, "run lacks the exact seeded mode and successful terminal marker")
    seed, terminal_cursor = seed_match.groups()
    events = parse_events(text, int(terminal_cursor))
    intrinsic_sites, workers, worker_frames = source_sites(snapshot)
    frame_steps = {
        match.start(): (int(match[3]), int(match[4]), int(match[5]))
        for match in STEP.finditer(text)
    }
    starts = list(STEP_START.finditer(text))
    ends = list(STEP_END.finditer(text))
    need(starts, "run log has no cursor-indexed core-step trace")
    need(len(ends) == len(starts),
         f"found {len(starts)} core-step starts but {len(ends)} core-step ends")
    for i, (start, end) in enumerate(zip(starts, ends)):
        need(start.start() < end.start(), f"coreStep {i} end trace precedes its start")
        if i + 1 < len(starts):
            need(end.start() < starts[i + 1].start(), f"coreStep {i} end trace is out of order")
    steps = [
        {"thread": int(start[1]), "cursor": int(start[2]),
         "pc": frame_steps.get(start.start()), "end_cursor": int(end[1])}
        for start, end in zip(starts, ends)
    ]
    step_cursors = [step["cursor"] for step in steps]
    need(all(a <= b for a, b in zip(step_cursors, step_cursors[1:])),
         "core-step choice cursors are not monotone")
    step_ends = [step["end_cursor"] for step in steps]
    need(all(start <= end for start, end in zip(step_cursors, step_ends)),
         "a coreStep ended before its start cursor")
    need(all(end <= next_start for end, next_start in zip(step_ends, step_cursors[1:])),
         "a coreStep end cursor passes the following coreStep start")
    need(step_cursors[-1] <= int(terminal_cursor),
         "last core-step cursor exceeds terminal choice cursor")
    need(step_ends[-1] <= int(terminal_cursor),
         "last coreStep end cursor exceeds terminal choice cursor")

    # Core step traces record the current MIR PC immediately before coreStep.
    # The atomic event executes inside the core::intrinsics::atomic_{load,store}
    # call dispatched from this wrapper MIR terminator. This captures the
    # event boundary, unlike the earlier Atomic::{load,store} caller.
    events_seen = []
    worker_thread = {}
    worker_ops = {"child_a": [], "child_b": []}
    for step in steps:
        if step["pc"] is None:
            continue
        frame_owner = worker_frames.get(step["pc"][0])
        if frame_owner is not None:
            worker_thread[step["thread"]] = frame_owner
        op = intrinsic_sites.get(step["pc"])
        if op is None:
            continue
        worker = worker_thread.get(step["thread"])
        if worker is None:
            continue
        if worker_ops[worker] and worker_ops[worker][-1]["op"] == "load":
            continue
        if op == "store" and not worker_ops[worker]:
            worker_thread[worker] = step["thread"]
            row = {"event": "Sx" if worker == "child_a" else "Sy",
                   "worker": worker, "op": op, "thread": step["thread"], "pc": step["pc"]}
            worker_ops[worker].append(row)
            events_seen.append(row)
        elif op == "store" and len(worker_ops[worker]) == 1:
            need(False, f"{worker} executed a second atomic store before its first load")
        elif op == "load" and len(worker_ops[worker]) == 1:
            need(worker_thread[worker] == step["thread"],
                 f"{worker} changed runtime thread between its store and load")
            next_cursor = step["end_cursor"]
            need(step["cursor"] <= next_cursor <= len(events),
                 f"{worker} atomic-load coreStep has an invalid choice-cursor interval")
            stale_events = [event for event in events[step["cursor"]:next_cursor]
                            if event["request"]["site"] == "atomicStale"]
            need(len(stale_events) <= 1,
                 f"{worker} atomic-load coreStep consumed {len(stale_events)} atomicStale choices")
            stale_input = stale_events[0]["input"] if stale_events else None
            row = {"event": "Ly" if worker == "child_a" else "Lx",
                   "worker": worker, "op": op, "thread": step["thread"], "pc": step["pc"],
                   "choice_cursor_interval": [step["cursor"], next_cursor],
                   "atomic_stale": stale_input}
            worker_ops[worker].append(row)
            events_seen.append(row)

    for worker, ops in worker_ops.items():
        need([item["op"] for item in ops] == ["store", "load"],
             f"{worker} did not execute exactly its first store then first load: {ops}")

    order = [item["event"] for item in events_seen]
    legal_orders = {
        ("Sx", "Ly", "Sy", "Lx"), ("Sx", "Sy", "Ly", "Lx"),
        ("Sx", "Sy", "Lx", "Ly"), ("Sy", "Lx", "Sx", "Ly"),
        ("Sy", "Sx", "Lx", "Ly"), ("Sy", "Sx", "Ly", "Lx"),
    }
    need(len(order) == 4 and tuple(order) in legal_orders,
         f"projected atomic intrinsic trace is not one of the six legal SC orders: {order}")

    return {
        "status": "PASS",
        "scope": "one actual canonical seeded replay; sampled event order only",
        "snapshot": str(snapshot),
        "snapshot_sha256": sha(snapshot),
        "run_log": str(run_log),
        "run_log_sha256": sha(run_log),
        "choice_event_count": len(events),
        "choice_inputs_all_within_recorded_support": True,
        "worker_definitions": workers,
        "atomic_intrinsic_order": order,
        "atomic_intrinsic_events": events_seen,
        "reported_seed": seed,
        "terminal": "exit_zero; leak_check=true; threads=3",
    }


def main():
    if len(sys.argv) != 4:
        raise SystemExit("usage: validate_orders.py SNAPSHOT RUN_LOG OUTPUT_JSON")
    result = check(sys.argv[1], sys.argv[2])
    Path(sys.argv[3]).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "seed": result["reported_seed"],
                      "atomic_intrinsic_order": result["atomic_intrinsic_order"]}))


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"validation failed: {error}", file=sys.stderr)
        raise SystemExit(1)
