#!/usr/bin/env python3
"""Assert the replay consumed the exact generated typed prefix and domains."""
import hashlib, json, pathlib, re, sys

def fail(message):
    raise SystemExit(message)

if len(sys.argv) != 4:
    fail("usage: validate_guided_choice_replay.py PREFIX_JSON LEAN_RUN_LOG OUTPUT_JSON")
prefix_path, log_path, output_path = map(pathlib.Path, sys.argv[1:])
prefix = json.loads(prefix_path.read_text())
log = log_path.read_text()
marker = "choice_events=#["
if marker not in log:
    fail("Lean replay log has no complete choice_events record")
trace = log.rsplit(marker, 1)[1]
chunks = re.split(r"\{ request :=", trace)[1:]
request_re = re.compile(r"Request\.(\w+)\s*\(Miri\.Interpreter\.ExecutionChoices\.(?:IndexSite|BoolSite|IntegerSite|ByteSite)\.(\w+)\)\s*([^,\n}]+)?", re.S)
input_re = re.compile(r"Input\.(index|boolean|integer|bytes)\s*\(Miri\.Interpreter\.ExecutionChoices\.(?:IndexSite|BoolSite|IntegerSite|ByteSite)\.(\w+)\)\s*([^\s,}]+)?", re.S)
if len(chunks) < len(prefix["inputs"]):
    fail(f"replay recorded only {len(chunks)} events, shorter than expected prefix {len(prefix['inputs'])}")
actual_inputs, actual_requests = [], []
for i, chunk in enumerate(chunks[:len(prefix["inputs"])]):
    req, inp = request_re.search(chunk), input_re.search(chunk)
    if not req or not inp:
        fail(f"cannot parse replay event {i}")
    req_kind, req_site, req_arg = req.groups()
    inp_kind, inp_site, inp_value = inp.groups()
    if req_kind != "index" and req_kind != "bernoulli":
        fail(f"unsupported replay request at event {i}: {req_kind}")
    if inp_kind not in ("index", "boolean") or req_site != inp_site:
        fail(f"unexpected replay input kind/site at event {i}")
    if inp_kind == "boolean" and inp_value not in ("true", "false"):
        fail(f"malformed replay Boolean at event {i}")
    if req_kind == "index":
        request = {"kind": req_kind, "site": req_site, "support": int(req_arg.strip())}
    else:
        request = {"kind": req_kind, "site": req_site, "rate_bits": int(req_arg.strip())}
    value = int(inp_value) if inp_kind == "index" else inp_value == "true"
    actual_requests.append(request)
    actual_inputs.append({"kind": inp_kind, "site": inp_site, "value": value})
for i, (actual, expected) in enumerate(zip(actual_requests, prefix["requests"])):
    if actual != expected:
        fail(f"request/domain mismatch at prefix position {i}: expected {expected}, got {actual}")
for i, (actual, expected) in enumerate(zip(actual_inputs, prefix["inputs"])):
    if actual != expected:
        fail(f"input mismatch at prefix position {i}: expected {expected}, got {actual}")
for target in prefix["target_events"]:
    i = target["prefix_index"]
    if i != target["event_index"]:
        fail(f"prefix/source event position disagreement in target metadata: {target}")
    if actual_requests[i] != {"kind":"index", "site":"atomicStale", "support":target["support"]}:
        fail(f"guided target request is not the declared binary stale choice at {i}")
    if actual_inputs[i]["value"] != target["guided_value"] or target["guided_value"] + 1 != target["support"]:
        fail(f"guided target did not select the oldest eligible value at {i}")
report = {
    "schema":"sc264-guided-choice-replay-validation-v1",
    "prefix_json":str(prefix_path),
    "prefix_json_sha256":hashlib.sha256(prefix_path.read_bytes()).hexdigest(),
    "replay_log":str(log_path),
    "replay_log_sha256":hashlib.sha256(log_path.read_bytes()).hexdigest(),
    "prefix_events_exact":len(prefix["inputs"]),
    "target_events":prefix["target_events"],
    "status":"PASS"
}
output_path.write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps(report))
