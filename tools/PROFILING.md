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
`--seed U64` and `--profile`; omitting the seed selects the
diagnostic zero policy. Explicit Lean runners require a prebuilt module closure.

To regenerate the large catch-panic workload after Rust/sysroot setup, build the
current exporter and select main explicitly:

```bash
bash tools/build-exporter.sh
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output scratch/catch-fresh.json --root main -- \
  tests/repro/unwind/catch_guest.rs --crate-name catch_guest
```

Unscoped exports also emit generic closure templates as independent roots and
can fail readiness. Use one unchanged export across every paired trial; a fresh
export of the same Rust source need not match a historical artifact's bytes.

A smaller completed collection workload is
`tests/repro/execution/vector-sort.rs`: it allocates 16 integers, sorts them,
and checks an iterator-based weighted checksum:

```bash
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output scratch/vector-sort.json --root main -- \
  tests/repro/execution/vector-sort.rs --crate-name vector_sort
bash tools/run.sh scratch/vector-sort.json --profile
```

Use the same exported file for both binaries; source paths and compiler allocation
identities can differ between fresh exports. Its successful outcome is
`finalized_exit code=0`. The native runner continues until a terminal/error
outcome or process interruption (Ctrl-C); it has no scheduler-iteration or
generated-choice cap. Diagnostic choices are generated on demand and retained
for replay, so longer runs still require host memory. Explicitly bounded
proof/test APIs retain `pending` for an incomplete prefix.

For hotspot attribution, `--profile` additionally reports complete scheduler
iterations taking at least 10ms as `execution.iteration_N.*`. The label records
the starting canonical body index as well as definition ID and MIR/unwind
location. The timed span includes scheduling and stack-empty callbacks; it is
not necessarily one MIR instruction. The Lean Options key
`leanMiri.iterationThresholdMs` overrides this local threshold for API callers.
The progress summarizer lists the slowest reported iterations separately from
sampled before/after completion boundaries. Below-threshold iterations are
absent, so the reported duration sum is incomplete.

Compiler metadata uses separate typed tables for types, layouts, function ABIs,
allocations, instances, spans, definitions and type constants. Import retains
numeric references. The runtime validates and reads the corresponding table
when an operation needs its compiler value. There is no generic JSON payload
graph or shared decoding cache.

Measure decoding, preparation and execution together as well as separately.
Changes that move work between these phases can improve one span without
improving total runtime. A schema change requires fresh exports from identical
Rust source, compiler configuration and guest settings; record both serialized
artifact hashes and sizes, and compare outcomes before interpreting timings.
