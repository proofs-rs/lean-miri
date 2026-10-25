# Current status and remaining work

This file is the sole entry point for known remaining work. Backlog triage does
not broaden the acceptance scope, semantics, theorem claims or test expectations.
Distinguish the existence of tests and historical successes from successful
execution in the current checkout. See the
[development guide](docs/development.md#check-commands) for check entry points
and prerequisites.

## Self-contained Lean test entry points

Self-contained Lean checks are collected under `MiriTests/` and registered with
Lake. `lake build MiriTests` checks all its modules; `lake exe miri_tests` reruns
registered runtime assertions even with cached builds. External comparisons and
input-dependent harnesses remain under `tests/`. This registration does not add
whole-machine proofs or turn historical results below into current reruns. See
[the test guide](tests/README.md#self-contained-lean-checks-miritests).

## Acceptance scope and current position

The scope includes common MIR, memory/Tree Borrows, Rust main startup
and exit, threads, synchronization, atomics, weak memory and data races. Finite
QA and general whole-machine proofs are separate goals. Overall completion and
the ability to verify arbitrary Rust are not claimed.

Records for the latest implementation before cleanup, `b747a48c`, were checked
against the code and subsequent results. There are finite success records for
shared frontend inputs, 77 maintained regressions (combined across multiple
attempts), 12 canonical cases, 4 SC controls, 16 decoder comparisons and 4 shared-ID
cases. A finite comparison of the large TB input also succeeded after re-exporting
the same Rust as schema3; the old schema2/900-second timeout is not counted as a
current unsupported feature. Additional SC diagnostic seeds 0–11 have success
records, observing 4 of the 6 store-before-load orderings. Sx,Sy,Ly,Lx and
Sy,Sx,Lx,Ly were not observed; this does not mean every schedule was tried.
These are not claims of successful reruns during this cleanup. Reusable
assertions, proofs and inputs have been moved into tests.

## Remaining general proofs (not acceptance conditions for current finite QA)

### Forward simulation from real steps to atomic events

The relation from [EvalCoreMachine](Miri/Input/EvalCoreMachine.lean),
[execution configuration](Miri/Input/EvalConfigurationCore.lean) and
[AtomicDispatch](Miri/Concurrency/AtomicDispatch.lean) to the
[local SC projection](tests/connected/proofs/ScProjection202.lean) remains unproved.
Next, define observations for the 4 X/Y events in real connected states and prove
that every permitted step stutters or extends the observations while preserving
static identity and each worker's store-before-load order. Re-enumerating the
6 local orderings does not resolve this. Resolution requires a kernel-checked
inclusion theorem for actual connected steps; reverse reachability of every
abstract ordering is not required.

### HB connection for join/reporting and correspondence with real memory

[JoinReadProof195](MiriTests/Connected/Proofs/JoinReadProof195.lean) is a local theorem
with HB assumptions. Worker reporting stores, termination clocks, successful
joins and main's result loads must be connected to
[Thread](Miri/Concurrency/Thread.lean),
[WeakMemory](Miri/Concurrency/WeakMemory.lean) and the real memory path.
Next, establish correspondence for HB assumptions, buffer/range identity and
initialized physical fallback reads, including intervening steps. Resolution
requires deriving the local theorem's assumptions from real connected states.

### Lift strict-choice normalization to the whole machine

[History erasure](MiriTests/Connected/Proofs/ChoicePublic217.lean),
[current-input locality](MiriTests/Connected/Proofs/ChoiceLocality220.lean) and
[demand](MiriTests/Connected/Proofs/DemandProof211.lean) are component theorems for
strict wrappers. Next, define a relation retaining fresh events and the unread
input suffix externally, and prove preservation by real machine steps.
Resolution requires a quotient theorem over the full machine relation.
It does not apply directly to seeded/bounded diagnostic policies, which require
separate assumptions and proofs.

### Exclude UB on every permitted finite prefix

No-(0,0) at normal termination alone does not exclude UB partway through a prefix.
The properties in [OperationalSafety](Miri/OperationalSafety.lean) still need
to be instantiated for the real connected machine and target inputs/contracts.
Next, use the connection lemmas above, handle all other nondeterministic choice
families or state fixed assumptions explicitly, and exclude reachable UB.
Unsupported, interpreter errors and fuel exhaustion must not become successes.
Resolution requires a kernel-checked theorem specifying the target, initial
conditions, external contracts and permitted choices.

The [connected graph explorer](tests/connected/proofs/ConnectedGraph215Schema3.lean)
and [exact state comparison](MiriTests/Connected/Proofs/ExactStateCodec207.lean) are
reusable. Earlier exploration was interrupted at 143,800 nodes with a remaining
frontier and no complete capture. No completion bound is established.
`bash tools/check-connected-proofs.sh` only typechecks these. Increasing the
budget of OPEN exploration does not resolve the proofs above.

## Validation gaps and pending checks within scope

### Compiler query closure and prepared allocation identity

General query closure remains unproved for the [exporter](exporter/src/main.rs),
[allocator_world](exporter/src/allocator_world.rs),
[CompilerAllocIdWorld](Miri/Input/CompilerAllocIdWorld.lean) and
[Decoder](Miri/Input/Decoder.lean). Subsequent implementations and finite
successes exist for entry function pointers, backtrace frame Instances, Offset
overflow pairs and memory-backed vtable providers; old gaps are not simply
repeated as current gaps. Next, retain inputs whose fresh exports expose actual
uncollected queries, and extend producer closure from their typed keys and source
operations. Resolution requires a reproduction for the target query to pass
fresh export → real connected execution while missing keys still produce
Unsupported. This task does not require query completeness for every program
or agreement with vanilla Miri's raw AllocId history.

Generate fresh [canonical cases](tests/connected/cases.py) with
`tools/export-connected.py`; replay fixed inputs with `tools/check-connected.py`.
Do not treat a dynamic vtable's CTFE salt0 probe as its runtime-salt ID.
Nonidentity erase/anonymize vtable queries were not observed in earlier small
inputs, and genuine producer→consumer validation for that branch remains pending.
Next, pin an input triggering the query and check the join between
[VTable](Miri/Interpreter/VTable.lean) and the compiler catalog. Resolution
requires a real-input comparison distinguishing 32 salts, type/predicate identity
and raw/dense IDs.

[Fresh erasure controls](tests/repro/README.md) and
`tools/check-vtable-erasure.py` distinguish an identity result from the required
nonidentity witness. Named HRTB syntax alone is insufficient: pinned rustc's
`PostAnalysisNormalize` erases/anonymizes successful MIR type queries before
the exporter collects them. A fresh before/after MIR dump of the retained HRTB
control confirmed that both named binders become anonymous while both unsize
casts and the Send predicate contrast remain. The exporter's
`struct_lockstep_tails_for_codegen` also normalizes when traversing struct-tail
fields, but does not unconditionally normalize its initial input pair; its
normalization assertion does not rewrite the caller's types. The static
borrowed-object control also retains an identity result. This explains these
controls, not every producer path: global symbolic vtables and recursively
discovered TraitVPtr demands also feed the query closure. Neither an identity
control nor a synthetic changed pair resolves this pending branch.

In the inspected source, [CTFE symbolic-vtable creation](upstream/rustc-source/compiler/rustc_const_eval/src/interpret/traits.rs)
erases/anonymizes before reserving the pair; [metadata decoding](upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/mod.rs)
preserves the encoded pair without normalizing it again. Additional inspection of
the [vtable provider at the pinned rustc commit](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_trait_selection/src/traits/vtable.rs#L133)
found late-bound-erasure/normalization before supertrait refs become TraitVPtr
entries. That provider is outside the selected local rustc source corpus; this
source tracing and the finite controls are not a general nonreachability proof.

Fresh control runs passed same-prepared-TyCtxt Miri exit-zero,
the query/catalog checks and connected exit-zero with leak checks. The HRTB
control retained two same-type/distinct-predicate queries and 64 salt results;
the static control retained one query and 32 salt results. A higher-ranked
second-supertrait upcast retained three queries and 96 salt results, including
distinct higher-ranked/instantiated principals sharing an exact memory-backed
vtable allocation. Its consumer now compares compiler-normalized principal
evidence while preserving the type, allocation, layout and entries checks and
the original symbolic predicate/salt identities. Forged principal aliases,
conflicting layout and missing normalization evidence are rejected. All six
queries were identity results; these controls do not resolve the nonidentity gap.

The [cross-crate metadata control](tests/repro/README.md) additionally builds an
rlib containing a public HRTB trait-object constant, then freshly exports a
separate consumer with no local concrete-to-dyn coercion. It passed
same-prepared-TyCtxt Miri and connected exit-zero, one thread and leak checking.
The root's evaluated external constant has a symbolic-vtable relocation; its
one query stayed identity and all 32 raw/dense/runtime salt joins passed. This
narrows the untested metadata path but is not a nonidentity witness.

Inspection of the complete compiler source archive at the pinned rustc commit
found two call sites of `reserve_and_set_vtable_alloc`: CTFE's already-normalizing
`get_vtable_ptr` and metadata decoding of the encoded pair. The constructor
itself does not normalize. Together with the previously inspected MIR
normalization and TraitVPtr provider, this gives a source-level reason to check
whether a noncanonical pair is reachable before adding more syntax variants.
The pinned [normalization provider](https://github.com/rust-lang/rust/blob/8144389c895da997dbdecaa635e41d6a50be6ffd/compiler/rustc_traits/src/normalize_erasing_regions.rs#L39)
also erases/anonymizes the resolved result after alias normalization; erasure is
not limited to the input before associated-type projections are expanded.
This source inspection and one metadata round trip do not prove that every
producer/decoder transformation preserves canonical identities. Nonidentity
producer-to-consumer validation remains pending; synthetic pairs or these
identity controls must not discharge it.

The optional `tools/check-vtable-erasure.py --trace-queries` diagnostic joins
producer collection sites to actual connected erasure lookups. Root/templates
can contribute catalog rows independently of runtime consumption. Nonidentity
mode therefore requires a changed pair to be consumed by the connected runtime,
in addition to the existing fresh reference, query and 32-salt checks. Neither
the existence of this diagnostic nor its parser unit tests resolves the pending
branch. Canonicality preservation across type extraction, metadata decoding and
recursive demand closure is still not a general nonreachability theorem.

Fresh traced comparisons passed same-prepared-TyCtxt Miri,
all 32 salt joins per catalog key and connected exit-zero with leak checks for
HRTB, upcast, static and cross-crate metadata controls. Their catalog query
counts were 2/3/1/1, while actual runtime erasure lookup counts were 2/2/0/0.
All seven query pairs stayed identity; the upcast's TraitVPtr child was not
consumed by the erasure lookup. Zero erasure calls does not negate the separate
global-allocation/metadata checks. Traced/untraced HRTB runs retained identical
export bytes and terminal output, including choice cursor 53. The reference
exporter reused the retained compiled Miri dependency closure; that closure was
not freshly rebuilt. These controls narrow coverage but do not resolve
nonidentity reachability or its pending producer-to-consumer witness.

### Execution performance and remaining hot interval

The same 278,818,016-byte export of
[catch_guest.rs](tests/repro/unwind/catch_guest.rs) now **finalizes as exit0**
with a compiled native runner. Earlier Lean --run executions timed out at
40 minutes without a raw result; that historical timeout no longer leaves
completion of this native diagnostic trace unresolved. The input SHA256 is
`034e3157806207389308d8777b1d2bfce95ee89f8a8dbe7663a8d187fb993012`.
The source sets a silent panic hook, catches one intentional panic, checks Err
and drops the payload. Its source workload is small; 279 MB is compiler metadata.

Build `native_runner` with the pinned Lake toolchain. `run.sh` now
uses this executable, preserving arguments and the existing bounded diagnostic
policy. The first C compilation is separate from execution timings; subsequent
invocations reuse the executable. The collector defaults to the same cached native build, freezing its executable
under the build lock before measurement. Explicit `--executable` skips building;
explicit `--runner` selects Lean --run with `--lean-path`. It records build-log
paths and mode/artifact hashes,
and forwards an optional u64 seed. The default no-seed policy is unchanged.

Three alternating sequential small-input pairs on CPU2, LEAN_NUM_THREADS=1,
with --profile, produced identical terminal/tape/event output in all six runs:
code822085532/cursor327. Lean --run wall times were 10.402/9.970/9.733 s
(CPU10.200/9.759/9.530, steal0.260/0.110/0.050); native times were
1.401/1.337/1.312 s (CPU1.395/1.330/1.308, steal0.020/0.010/0).
Throttling was zero. The ratio of sample median wall times is 7.46.
This finite comparison does not prove all executions compiler-equivalent.

These performance samples use the runtime frozen before merging main `6789b53a`;
they have not been repeated on that integrated runtime. Integration validation
passed the native build, all five profile identity axiom checks, quick checks
(55 Python tests) and the small native exit822085532/cursor327 replay. Logs are
in ignored `scratch/merge-pr9/`.

The large-input native replay with --profile completed on candidate0 in **420.606 s wall**,
420.425 s CPU, steal4.210 s, wall-minus-steal approximation416.396 s, with
zero throttling and unchanged memory.events. Peak process-group RSS was
3.496 GB. Builds and other benchmarks did not overlap the timed samples.
Runtime/harness sources matched the frozen bytecode baseline by hash, and
input/binary/module hashes remained unchanged afterwards. This is one large
native trial; there is no matched whole-run speed ratio because bytecode did
not finish. It ran the existing no-seed bounded diagnostic policy.

| Native large-input phase | Observed wall seconds |
| --- | ---: |
| Read/decode, blocking obligations 0 | 177.369 |
| Lower | 7.728 |
| Preparation | 42.337 |
| Setup/negative preflight | 2.649 |
| Bootstrap | 12.731 |
| Bootstrap-to-raw-result | 174.722 |
| Outer finalization | 0.005925 |
| Total process including output | 420.606 |

The first 184 sampled before/after scheduler labels exactly matched the
historical bytecode replay. The native trace then emitted 396 sampled boundaries,
reached main_exiting/tls_done and finalized exit0/cursor2640. Raw exit, finalizer,
leak-check/walk and candidate0 markers appeared in order. Actual leak-walk
shape was live39/root entries22/edges17; export allocation counts are not live
allocation counts. A finite finalized result is not UB freedom over all choices.

The formerly unresolved123-second interval is attributed in the analysis below.
The implementation and validation results are recorded below.
The earlier two catch_unwind ReifyFnPointer iterations took 21.015/21.102 s
under --run but only 0.060757/0.060249 s natively, so their old wall times are no
longer the best optimization target. Outer leak checking took milliseconds.
The five generic profile identity checks remain available in
[FinalizationProfileIdentity2026](MiriTests/Input/FinalizationProfileIdentity2026.lean).
They preserve Lean states and bounded outcomes; they do not verify native C
compilation or all Rust executions.

The small no_std function-pointer control also finalized42 natively in1.275 s
(CPU1.269, steal0.040), matching its bytecode and vanilla-Miri expected42.
The regular wrapper finalized the original small input in both normal mode
(cursor327) and --seed0 --profile (cursor339). Native build passed1244 jobs;
quick checks passed54 Python tests plus source/fixture checks. New collector
checks cover native launch without LEAN_PATH, seed forwarding/u64 rejection and
mutually exclusive runner selection. Full check.sh/performance-regressions.sh
and same-prepared-TyCtxt Miri comparison remain unexecuted.

Vanilla pinned Miri's prior catch-source trials were silent exit0 in
0.266/0.165/0.166 s wall (CPU0.236/0.154/0.154; steal0.030/0.010/0,
throttling0). They include compiler-driver invocation but exclude toolchain/
sysroot builds. They do not match the prepared TyCtxt/AllocId history of Lean's
export, so no strict slowdown ratio is claimed. The fresh export took91.449 s,
separate from both execution measurements.

Current logs, frozen binary, manifests, trial/trace assertions and summaries
are in ignored `scratch/native-comparison/`. Binary SHA256:
`4aa45fe398e6b5ae6675fab7e0985912bb8de05f07ce70e41ce2177922bf6f8d`.
Historical evidence remains under `scratch/execution-progress/`,
`scratch/finalization-probe/main-99644c50-001/`,
`scratch/large-input-investigation/` and `scratch/catch-reference-probe/`.
Follow the performance protocol in [AGENTS](AGENTS.md) and [README](README.md).

The collector-default follow-up passed two separate default invocations with
identical frozen binary hashes and no C compilation/relink in either cached
build log. Both finalized code822085532; the explicit --runner bytecode path
also retained that result. Build failure aborts before execution, and snapshot
immutability is tested. Latest quick checks passed55 Python tests. These
follow-up logs and summaries are in ignored `scratch/measure-default/`.

### Caller-location and decoder optimization

The two optimizations are implemented on the analysis branch, with main
`fd2a981f` integrated before changes (its post-#9 additions were documentation
and control inputs). The native baseline binary is the frozen analysis binary;
its SHA matches `scratch/native-hotspots/profiled-native`. No guest semantics,
checks or choice constraints were intentionally changed.

**Caller-location:** [callerLocation](Miri/Input/CompilerValueConstants.lean)
still processes all43,827 rows in source order, including malformed nonmatching
rows, but builds a CompilerSpanInterner once per demand. Candidate buckets retain
full SourceSpanData comparison and first matching index. Every row starts from
the same base, so missing spans cannot append into subsequent rows' tables.
The checked same-array comparison avoids deep equality for unchanged tables;
its equality to the original comparison is kernel-checked. The old query is
retained as callerLocationReference for parity tests. This is a batch span-index
optimization, not a constant-time catalog cache. Runtime Location allocation,
provenance, roots and failed-prefix handling remain in the unchanged materializer.

**Decoder:** [JsonTraversalCache](Miri/Input/JsonTraversalCache.lean) runs the
authoritative SharedPayloads resolver first, then constructs parallel cached
hashes bottom-up using the transport DAG. The actual resolved Json is retained.
Four existing DFS validators/collectors use keys containing that Json and its
cached structural hash. Key equality remains the original Json equality, never
hash/ID equality, so equal distinct nodes deduplicate and collisions still
compare values. Checks, traversal/phase order, paths and ABI result order remain.
Noncanonical raw objects or unexpected shapes fall back to ordinary hashing;
no lawfulness of arbitrary Raw Json is assumed. No semantic check is delegated
to the cache. Both runtime and full decoders use it; uncached reference entry
points remain for differential checks. Hash caching adds about2.7 seconds to
input processing, included in total decode time below. Nested native profiler
reports are self times; the parent resolution span excludes this child span.

Same278,818,016-byte input, immutable native binaries, CPU2 and one Lean thread.
Order: candidate1, baseline1, candidate2, baseline2. No builds/other benchmarks
overlapped. All4 runs finalized exit0/cursor2640, with byte-identical consumed
tapes and choice events, unchanged hashes/memory.events and zero throttling.

| Trial | Baseline wall / CPU / steal seconds | Candidate wall / CPU / steal seconds |
| --- | --- | --- |
| 1 | 442.595 / 441.978 / 4.820 | 201.197 / 201.086 / 2.080 |
| 2 | 421.536 / 421.359 / 4.890 | 208.099 / 208.015 / 2.520 |
| Wall median | 432.065 | 204.648 |

The median ratio is2.11x, a52.6% wall-time reduction on this fixed diagnostic
input. It is not an arbitrary-program claim. Raw wall-minus-same-CPU-steal
approximations are437.775/416.646 s baseline and199.117/205.579 s candidate;
they are not CPU time. Peak process-group RSS was3.493–3.507 GB baseline and
3.368–3.462 GB candidate. Export and lean-miri compilation are separate budgets.

| Phase wall median (seconds) | Baseline | Candidate |
| --- | ---: | ---: |
| Read/decode, including hash preparation | 178.374 | 86.109 |
| Lower | 7.765 | 7.498 |
| Preparation | 45.378 | 42.198 |
| Setup/negative preflight | 2.751 | 2.712 |
| Bootstrap | 12.100 | 12.061 |
| Bootstrap to raw result | 182.880 | 51.426 |
| Outer finalization | 0.008 | 0.007 |

The directly timed caller-location iteration2353 fell from122–136 s to1.3 s.
On trial2, the four hash-keyed decoder phases fell from133.2 s combined to
38.79 s; runtime-value decoding remains26.4 s and was not optimized. Differences
in unchanged preparation/lower phases are not attributed to these changes.
The small control matched code822085532/cursor327/tape/events at1.343 s baseline
and0.968 s candidate; this is one control pair, not a small-input benchmark suite.

Validation: native build passed1246 jobs. Full
`tools/check-performance-regressions.sh` passed, including the added cached/
uncached decoder, caller-location error/order and hash-cache tests; its axiom
audit passed70,661 declarations with only propext/Quot.sound/Classical.choice.
The original generic decoder profiling identity remains unchanged and typechecks.
The independent decoder goldens passed16 schema-3 cases plus4 shared-ID cases.
Cached/uncached decoding also matched readiness, ordered obligations and ABI/body
payload sequences on those16 cases and malformed ABI/vtable precedence probes.
Cache tests audit actual hashes/child correspondence, inline/shared duplicates,
noncanonical fallback and transport errors. Caller tests compare the old query
on success, equal/conflicting rows, malformed headers/rows, coarse-key collisions,
missing spans and range-guard precedence. Quick checks passed58 Python tests.

A fresh [same-site repeated-caller control](tests/repro/compiler-queries/caller-location-repeat.rs)
requires two runtime Location roots to have different allocation IDs. Its fresh
prepared export finalized42/cursor340 on baseline and candidate with matching
tapes/events. Vanilla pinned Miri also returned42. This independently checks
freshness, but does not match Miri's full prepared TyCtxt/AllocId history.
The native synthetic hash probe also matches cached/uncached digests, including
the root object. It is a mechanism check, not a Rust speedup measurement.

No full generic indexed-query/decoder equivalence proof is added: the component
identities, old-query parity, independent golden diagnostics and finite guest
comparisons have the scopes stated above. Full check.sh and a new same-prepared-
TyCtxt Miri comparison of the large guest were not run. Raw manifests, all
attempts, frozen binaries,4 large trials, control export/reference, paired hashes
and audits are in ignored `scratch/native-optimization/`.

Remaining priorities are runtime-value decoding, the residual equality/validation
work within decode, and preparation call resolution (about22 s). Caller-location
still scans the catalog, but now costs about1.3 s here; do not prioritize a guest
pointer cache or skip checks to remove it. Prepared-input reuse can amortize
multiple seeds only with input/version/config binding and fresh guest state; it
does not replace first-run improvements or justify reusing allocation identities.

## Feature support outside the current acceptance scope

The following support and integration work remains in the backlog, even though
it is not required for current main/parallel-Rust acceptance. Retaining a task
here does not imply that the whole feature is unimplemented: existing support
and validation gaps must be checked against pinned upstream before extending it.
Preserve existing implementations and fail-closed Unsupported outcomes.
WP remains deferred with its implementation removed. GenMC support has been removed;
the interpreter supports disabled race tracking and the Miri vector-clock backend.

* **Windows / peripheral OS facilities** —
  [WindowsPlatform](Miri/Interpreter/WindowsPlatform.lean), MiriTests/Native/ and
  Unix tests. Target ABI, all shims and real-host connections are not guaranteed.
  On resumption, resolution requires reproducing missing capabilities with a
  fixed target and genuine input, then comparing the shim's ABI, state and errors.
* **Native guest and math boundary** — [native](native/),
  [NativeMathHost](Miri/Input/NativeMathHost.lean), tools/NativeRunner.lean,
  tools/NativeMathBoundaryQA.lean and MiriTests/Native/. Separate host callbacks from
  numerical equivalence. `tools/check-powi-zero.py` passed fresh
  same-prepared-TyCtxt Miri and connected exit-zero with leak checks for 16
  exact positive-one bit assertions: f32/f64 exponent zero with positive/negative
  finite values, signed zeros, infinities and quiet NaNs. Fresh MIR retained both
  intrinsic calls with runtime bases and constant-zero exponents. This uses the
  fixed-result path, not a numerical host callback, and the no_std `miri_start`
  entry, not std main. Signaling-NaN nondeterministic choices, other
  widths/exponents, f128 and broader absent-host validation remain pending.
  On resumption, generate a reference from the
  same Rust and compare real-host bits and Unsupported outcomes. Helper-mock
  success does not resolve this.
  The finite `tools/check-math-nohost.py` run passed fresh
  same-prepared-TyCtxt Miri references for f64 sin(1) and fixed cos(0). Both
  connected guests exited zero with the native host; without it, sin reached
  the exact unary-capability Unsupported (explicitly not guest success), while
  cos retained exact 1.0 bits and exited zero with leak checking. Two negative
  invocations rejected the wrong terminal expectations. This closes those two
  absent-host controls only; other operations, widths and NaN cases remain open.
* **Timezone** — [source and assumptions](docs/chrono-tz-source-port.md),
  MiriTests/Regression/TimezoneGuestEnv.lean and `tools/check-timezone.py`.
  Eight genuine `localtime_r` calls passed fresh connected Lean
  execution and standalone pinned Miri on the same Rust/compiler flags/sysroot:
  absent/UTC TZ, invalid name/UTF-8 fallback, the second before the epoch, a
  leap day, New York's spring DST boundary and Kathmandu's fractional offset.
  All nine integer tm fields, gmtoff and numeric NUL-terminated zone strings
  were asserted; Lean required exit-zero, one thread and a successful leak check.
  The reference explicitly disabled isolation and used a separate TyCtxt from
  export. Lean consumed an ordered finite trace from a real retained Linux
  epoll, one monotonic-clock observation and 278 of 512 observed empty
  nonblocking polls; unobserved host demands remain Unsupported. This does not
  establish general host integration, all-zone/date equivalence or timestamp
  endpoint/out-of-range behavior. Next, extend genuine comparisons to those
  remaining date-range boundaries; table generation/count checks alone do not
  resolve them.

## Integrated regression validation

`bash tools/check.sh` completed with exit status 0 against
`1cf5fb9a` in a separate worktree, without implementation changes. This closes
the pending full producer-to-runtime regression for that revision. The run
included 48 Python tests, 6 Rust analyzer tests, Lean builds, an axiom audit of
70,527 declarations (only the 3 permitted axioms), maintained component
comparisons, fresh exporter/input/frontend/runtime-metadata checks, fresh
exported-MIR execution comparisons with pinned Miri, and the final obligation
inventory diff. The eval-core cases used hash-checked, adapted schema3 unit
fixtures rather than fresh exports.

The pinned Lean/Rust installations and existing reference Miri binary and
MIR-enabled std sysroot were reused; the reference environment was not freshly
constructed. Lake artifacts were copied into an independent writable directory
and checked by the builds. Build calls were serialized with
`/tmp/lean-miri-lake-build.lock`; fixture execution did not hold that lock.
The full-run log is in ignored `scratch/logs/full-locked.log` in that worktree.

This result covers the checked revision only. The separate canonical12,
ordering, large-TB, SC-schedule, connected-proof and structural-regression entry
points were not rerun in this pass. It does not validate later changes, establish
large-input completion or performance, or resolve the general proofs and query
closure gaps above.

## Historical checks from the earlier repository cleanup

The cleaned-up files were placed in a separate directory and the
checks below were run without copying existing `.lake`, target, working scratch
or reference Miri/sysroot. Installed pinned Lean/Rust compilers and the Cargo
registry cache were reused as external dependencies. These are historical results
for the cleanup revision, not reruns on the current branch. Logs are in ignored scratch; this table records reruns
after fixes. Intermediate setup failures and unexecuted checks are not counted
as successes.

| Check entry point | Result and scope |
| --- | --- |
| `bash tools/check-quick.sh` | PASS. 48 Python tests, pin/source audit, semantic lint, expected inventory and fixed-fixture hashes. |
| `bash tools/check-build.sh` | PASS. Built from empty Lake artifacts, including ExecutionChoicePolicy needed for replay. Final axiom audit: 70,254 declarations, only the 3 permitted axioms. |
| `cargo test --locked --offline --manifest-path source-analysis/Cargo.toml` | PASS, 6 Rust analyzer tests. |
| Pinned Cargo `check --locked --offline --manifest-path exporter/Cargo.toml` (ordinary / `--features miri-reference`) | Both configurations PASS. Missing crates fetched without changing the lock. This is not successful guest/Miri execution. |
| `bash tools/check-decoder.sh` | PASS. 16 comparisons with saved expectations from an independent old decoder, plus 4 shared-ID cases. |
| `bash tools/check-connected-proofs.sh` | PASS. Kernel checks for 18 component modules and graph-runner typechecking. All 64 printed axiom dependencies are permitted. This is not a whole-machine safety proof. |
| `python3 tests/connected/compare_selector.py` | PASS. Finite multiset comparison for SC6 / Relaxed20 extracted from pinned source. This does not run the Miri interpreter. |
| `bash tools/check-structural-regressions.sh` | PASS. Additional typechecking, kernel examples, #eval and no-input runtime assertions for zero width, indexes/duplicate order, crosswalk and clock reuse. Supplemental guests requiring arguments were not run. |
| `python3 tools/check-connected.py` | PASS, all canonical12 replays. Checked classification of 9 normal + 3 expected UB, fixed expected output and unchanged sources/OLean. Reference Miri reused retained same-TyCtxt results. |
| `python3 tools/check-connected.py --ordering` | PASS, 4 controls. Compared typed prefixes, worker-operation/scheduler order, weak (0,0) and SC candidate-domain restrictions. |
| `python3 tools/check-connected.py --large-tb --timeout 1800` | PASS. Frozen child write on the same Rust input; matched source line 14 / MIR bb1[8], 1 thread and 44 choices. |
| `python3 tools/check-sc-schedules.py` | PASS, all 12 executions for seeds 0–11, observing 4 orderings. Rejected 3 negative logs for truncation, out-of-support input and missing post-step records. |

In that historical run, unexecuted checks included **fresh construction of reference Miri and the
MIR-enabled std sysroot, and full regression `bash tools/check.sh` from fresh
exports**.
That historical run was limited to a fresh Lean build,
saved-input replay and local checks; it did not include fresh construction of
the heavy reference environment. Do not count that work as successful.
To rerun, follow README setup/fetch, then
`bash tools/setup-miri-reference.sh` → `bash tools/check.sh`.
Start individual genuine re-exports with `tools/export-connected.py`.
Out-of-scope Windows/native validation and the general proofs above were
also not completed in this run.
