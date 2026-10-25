# Profiling and performance measurement

Run commands from the repository root after the [README setup](../README.md#prerequisites-and-setup).

Use `tools/measure.py --help` to remeasure performance.
Pass a separately pinned OLean closure to `--lean-path`, and alternate old and
new versions using the same input, CPU and 1 Lean thread. Record raw wall/process
CPU time, steal on the same CPU and cgroup throttling under `scratch/performance/`
(configurable). Do not build concurrently, and compare the spread across multiple
trials. Wall−steal is an approximate supplementary metric.
`terminal_observed` means terminal output was observed, including Unsupported;
it is not a success or safety verdict. Compare the actual terminal outcome with
the expected value separately. Main-process wall time also includes the
collector's delay in observing completion.

For decode/lower/preparation breakdowns, pass
`--runner tools/ProfilePreparation.lean` to the same collector. It enables the
existing definitionally transparent profilers and reports input sizes and
call/body/function query-table counts. `preparation_only_observed` means strict
readiness and preparation completed; it does not execute the guest, so
`terminal_observed` and `finalized_exit_observed` remain false. Distinguish
internal profiler spans from wall/CPU intervals observed by the parent process.

For native decode-only measurements, build `lake build profile_runtime_decoder`,
freeze `.lake/build/bin/profile_runtime_decoder` under the build lock, then pass
that snapshot to `measure.py --executable`. It accepts only the input path and
always enables decoder profiling, including separate `decoder.json_parse` and
`decoder.runtime_value` spans. Strict readiness must pass; `decode_only: complete`
reports decoding only, without lowering, preparation or guest execution. The
collector records raw wall/CPU and host counters, but neither `terminal_observed`
nor `preparation_only_observed` should be true for this entry point. Use the same
alternating artifact/input/CPU protocol as a full run. This isolates decoder
costs; it does not measure a whole-program speedup or a different wire format.

To profile a complete execution, use
`bash tools/run.sh INPUT.json --profile` (after any `--seed U64`),
or pass `--profile` to `tools/measure.py`. This enables the existing
decode, preparation and startup profilers while retaining guest execution and
finalization. The collector records the first candidate's bootstrap boundary;
later choice-repair candidates do not overwrite it.

Full profiles also emit `finalization.raw_result.*` before calling the exit
finalizer, `finalization.start`/`complete`, and leak-check/walk start/end markers.
Walk-start markers include actual live allocation, root and edge counts. The
collector separates post-bootstrap execution from finalization and leak checks
for the first candidate. A raw exited result is not a finalized process result;
thread and leak checks still run before `finalized_exit` can be reported.

Full profiles additionally sample `execution.before`/`after` boundaries for the
first 64 outer scheduler iterations and every 64th thereafter. Each records the
active thread, stack depth, function definition ID, MIR/unwind location and
main/TLS stage. These are scheduler iterations, not MIR instruction counts;
`main_running` can include the std start wrapper. No heap or local values are
serialized. To summarize the first candidate from a collector run, use
`python3 tools/summarize-progress.py PATH-TO-RUN-01.json`. Its completed
iteration count is a lower bound from sampled after boundaries. Sampling gaps
cannot establish that the last reported frame is stuck or that main returned.

The summary's `process_finalized_exit_observed` describes terminal output from
the whole process, including later repair candidates; it does not certify the
sampled first candidate. `tools/run.sh` builds and runs `native_runner`; input checks,
choices, guest execution and finalization use the same harness. The initial
native build compiles C objects and is excluded from execution timings.

`measure.py` also defaults to building `native_runner`. It uses the
same build lock as `run.sh`, copies the executable to a private snapshot
while holding the lock, then releases the lock before measuring. Build checks
and compilation are excluded from all measured execution times. Repeated calls
reuse Lake's cached build when sources and dependencies are unchanged.

For an already frozen native binary, pass
`--executable /absolute/path/to/native_runner`; this skips building.
For Lean `--run`, explicitly pass `--runner tools/Run.lean` and
`--lean-path FROZEN_LIB`. These modes are mutually exclusive. The collector
records execution mode, artifact hash and any build-log path. Both modes accept
`--seed U64` and `--profile`; omitting the seed preserves the existing bounded
diagnostic zero policy. Explicit Lean runners require a prebuilt module closure.

For hotspot attribution, `--profile` additionally reports complete scheduler
iterations taking at least 10ms as `execution.iteration_N.*`. The label records
the starting canonical body index as well as definition ID and MIR/unwind
location. The timed span includes scheduling and stack-empty callbacks; it is
not necessarily one MIR instruction. The Lean Options key
`leanMiri.iterationThresholdMs` overrides this local threshold for API callers.
The progress summarizer lists the slowest reported iterations separately from
sampled before/after completion boundaries. Below-threshold iterations are
absent, so the reported duration sum is incomplete.

The diagnostic `lake build profile_json_sharing` target constructs compact
shared JSON DAGs and times structural hashing. Run its executable separately
from application benchmarks, with the same CPU/thread controls. It demonstrates
hash traversal scaling; it does not measure the fraction of decoder time spent
in hashing or establish an application speedup.

The decoder reuses structural JSON hashes computed from the validated transport
DAG, including runtime-value memo keys; full JSON comparisons, decoding context,
diagnostic rebasing and all validation phases remain. Noncanonical Raw
objects fall back to ordinary hashing. `decodeRuntimeJsonReference` and
`decodeJsonReference` run the uncached path for regression checks. Caller-location
queries reuse a span index within each demand; runtime Location roots remain
fresh per intrinsic evaluation. See [STATUS.md](../STATUS.md) for the measured input, limits and
remaining costs, and `tools/check-performance-regressions.sh` for parity checks.
