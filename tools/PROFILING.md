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

The decoder retains the exporter's document-local shared-node IDs. Runtime-value
memoization and validation visits use those IDs; inline values and cheap scalars
are traversed directly. Context flags and diagnostic rebasing remain per
occurrence. Structural hashes remain for value-based ABI deduplication, and
noncanonical Raw objects retain the original full-value key comparison/hash.
`decodeRuntimeJsonReference` and `decodeJsonReference` run the uncached traversal
path for regression checks; neither bypasses validation.

Import-time `decoder.compiler_abi_queries` and `decoder.compiler_values` spans
prepare complete typed FnAbi/generic-argument/span projections for the native
runtime input. Preparation still converts and validates ABI results against the
current runtime. `prepare.typed_abi_index` replaces per-call linear scans of
source ABI payloads. Since work moves from preparation into decoding, compare
whole-process and combined decode/preparation costs rather than interpreting a
shorter preparation span alone as a speedup. Diagnostic/reflected imports retain
the schema-only document and use the compatibility path.

Caller-location queries reuse a span index within each demand; runtime Location
roots remain fresh per intrinsic evaluation. See [STATUS.md](../STATUS.md) for
measured inputs, limits and remaining costs, and
`tools/check-performance-regressions.sh` for parity checks.

## CPU sampling without perf_event access

`tools/cpu-sample.c` is an optional Linux x86-64 preload diagnostic. It records
monotonic timestamps, interrupted instruction PCs and thread IDs every 4ms of
process CPU time. It owns SIGPROF/ITIMER_PROF during that diagnostic run.
It samples only the exact executable specified by
`LEAN_MIRI_SAMPLE_EXE`, so helper version probes do not overwrite its output.
Use a unique, existing scratch directory and prefix for each matching process.
It does not change Lean/Miri sources or provide a guest safety verdict.

```bash
mkdir -p scratch/cpu-sampling
cc -shared -fPIC -O2 -Wall -Wextra tools/cpu-sample.c \
  -o scratch/cpu-sampling/pc.so
# Use an already frozen executable and the same validated arguments as control.
LEAN_MIRI_SAMPLE_EXE="$(realpath scratch/frozen-native)" \
LEAN_MIRI_SAMPLE_OUTPUT="$PWD/scratch/cpu-sampling/first" \
LD_PRELOAD="$PWD/scratch/cpu-sampling/pc.so" LEAN_NUM_THREADS=1 \
  taskset -c 2 scratch/frozen-native INPUT.json --profile
python3 tools/summarize-cpu-samples.py scratch/cpu-sampling/first
```

For caller PCs, install libunwind development headers and additionally compile
with `-DWITH_LIBUNWIND -lunwind`. This uses libunwind's local signal-frame
unwinder and records up to 32 callers; summarize these records with
`--stack-depth 32`. The PC-only mode needs no libunwind dependency. Symbolization
runs offline using `nm` and `readelf`; the header mapping supplies the correct
PIE bias even when lld inserts pages between LOAD segments. Nonzero-address
PIE headers and truncated records are rejected rather than guessed.

With the corresponding `measure.py` run JSON, `--phases RUN.json` attributes
samples to decoder/lowering/preparation/bootstrap/execution boundaries.
`--leaf-span PROVIDER.NAME` additionally selects a reported interval known to
contain no nested profiler calls; exclusive parent profiler times cannot be
used as inclusive interval lengths. Sampling is diagnostic attribution, not a
speedup benchmark: keep an unsampled control and verify complete outcomes.

Exclusive counts describe the interrupted PC; cumulative counts count each
symbol at most once per sampled stack and overlap with callers. Truncation can
omit upper callers. Linked identical-code folding may name a generic helper
after another specialization, so use its callers and source code before
attributing ownership. Do not sum cumulative percentages or convert them into
an assumed removable wall time. Sampling overhead and shared-host variation
require separate verification of any subsequent optimization.

## Summarize saved exporter profiles

Run `python3 tools/summarize-exporter-profile.py EXPORTER.log` to summarize
saved `export_profile:` spans. Repeated spans retain individual values and call
counts. Parent spans include children; do not add nested totals together.
The summary describes attribution, not guest safety or a measured speedup.

Logs containing all four direct-mode `export_profile_at:` boundaries additionally
separate driver time before/after the export callback. Incomplete, repeated or
out-of-order boundaries are rejected. Older span-only logs produce no invented
driver intervals. Optional domain/catalog records preserve counts; the historical
`emitted_mir` field is labeled `processed_instances`, since it counted processed
requests rather than emitted bodies.

This offline tool can analyze retained experiment logs without changing the
exporter. Additional event production is a separate change.
