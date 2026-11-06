# Current status and remaining work

This file is the sole entry point for known remaining work. Backlog triage does
not broaden the acceptance scope, semantics, theorem claims or test expectations.
See the [development guide](docs/development.md#check-commands) and
[test guide](tests/README.md) for check entry points, prerequisites and coverage.
Historical successes do not establish successful execution in the current checkout.

The acceptance scope includes common MIR, memory/Tree Borrows, Rust main startup
and exit, threads, synchronization, atomics, weak memory and data races. Finite
QA and general whole-machine proofs are separate goals. Overall completion and
the ability to verify arbitrary Rust are not claimed.

## Empty-function caller-domain transport

The [empty-function proof](examples/empty_function/README.md) covers actual call
initialization and every finite in-call prefix under its explicit `Metadata`,
`Profile`, `RuntimeProfile` and `CurrentInputDraft` assumptions. A theorem that
every Rust-valid caller state satisfies this domain remains absent. The domain
includes raw caller, representation, pointer/source, memory/borrow, address/ID
and runtime coherence; agreed pure metadata facts remain explicit assumptions.
Compiler/exporter correctness and Rust/interpreter correspondence remain trusted.

The target admits checked non-UB stops, including resource exhaustion; it does
not claim normal return or NoErrors for every resource supply. Allocator
coherence is guarded by active raw runtime and enabled-source counters, rather
than excluding zero/wrapped counters, exhaustion flags or the final MAX ID.
The exact race-off/shallow/fixed-scheduling profile is in `Specification`;
other scheduler interleavings and caller execution after return are outside scope.

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
reusable, but exploration has no complete capture or established completion bound.
`bash tools/check-connected-proofs.sh` only typechecks these. Increasing the
budget of OPEN exploration does not resolve the proofs above.

## Validation gaps within scope

### Hosted regressions and coverage

A successful hosted three-lane regression rerun remains required after the
`MiriTests/Rvalue/Rvalue.lean` assertion elaboration fix and the hosted ripgrep
setup fix. These fixes do not establish the complete comparisons/replays or the
later exporter and fresh-input/execution phases that the failures prevented.
See [CI coverage](tools/ci/README.md) for lane commands and artifacts.

Timezone also needs a successful hosted rerun. Its CI wrapper failed before
guest execution because its libc filename glob did not identify exactly one
archive; the match count and paths were not logged. The Cargo compiler-artifact
selection fix needs hosted validation rather than relying on the old glob.

Fresh regeneration/comparison of every canonical and focused guest, the complete
argument-driven query-demand suite and standalone unregistered harnesses remain
outside workflow coverage. Saved replay cannot validate changed producers.
Selected finite checks do not close general proof or source-correspondence gaps.

The latest shared-node/typed-metadata optimization revision still needs full
`tools/check.sh`, the full `miri_tests` runtime registry and a fresh
same-prepared-TyCtxt reference-Miri comparison. The full regression result for an
earlier revision does not validate later changes. Separate canonical12, ordering,
large-TB, SC-schedule, connected-proof and structural-regression entry points
also need current-revision execution. Fresh construction of the reference Miri
and MIR-enabled std sysroot remains a validation gap; reusing retained artifacts
does not establish that setup path.

### Compiler query closure and prepared allocation identity

General query closure remains unproved for the [exporter](exporter/src/main.rs),
[allocator world](exporter/src/allocator_world.rs),
[CompilerAllocIdWorld](Miri/Input/CompilerAllocIdWorld.lean) and
[Decoder](Miri/Input/Decoder.lean). Retain genuine fresh exports exposing
uncollected queries and extend producer closure from their typed keys and source
operations. A target reproduction must pass fresh export → real connected
execution while missing keys still produce Unsupported. This does not require
query completeness for every program or agreement with vanilla Miri's raw
AllocId history. Entry function pointers, backtrace frame Instances, Offset
overflow pairs and memory-backed vtable providers already have implementations
and finite controls; investigate actual missing queries before extending them.

Nonidentity erase/anonymize vtable queries still lack genuine producer-to-consumer
validation. Pin a triggering input and check the join between
[VTable](Miri/Interpreter/VTable.lean) and the compiler catalog, distinguishing
all 32 salts, type/predicate identity and raw/dense IDs. A dynamic vtable's CTFE
salt0 probe is not its runtime-salt ID. Use [erasure controls](tests/repro/README.md)
and `tools/check-vtable-erasure.py --trace-queries`: a changed catalog pair must
actually be consumed by the connected runtime, alongside fresh reference,
query/catalog and salt checks. Catalog rows from roots/templates or TraitVPtr
children do not establish runtime consumption. Identity controls and synthetic
changed pairs cannot discharge this branch.

Before adding syntax variants, investigate whether noncanonical pairs are
reachable. Pinned rustc normalizes/erases successful MIR queries, CTFE vtable
creation and TraitVPtr principals; its normalization provider also erases the
resolved result after alias normalization. Struct-tail traversal normalizes
fields without unconditionally rewriting its initial input pair. Metadata
decoding preserves the encoded pair, and `reserve_and_set_vtable_alloc` itself
does not normalize. HRTB, upcast, static and cross-crate metadata controls have
retained identity pairs only. These controls and source tracing do not prove
canonicality preservation across type extraction, metadata decoding and recursive
demand closure, or general nonreachability of nonidentity pairs. The TraitVPtr
provider lies outside the selected local rustc source corpus.

### Performance and optimization assurance

Remaining performance work includes runtime-value decoding, residual equality
and validation work, and preparation outside the optimized call-resolution
lookup. Caller-location still scans its catalog; optimization must retain
source-order diagnostics, malformed-row handling and fresh Location allocations.
Measure current immutable artifacts with the protocol in [AGENTS](AGENTS.md);
old timings and shared-host samples do not establish a general speedup.

No full generic indexed-query/decoder equivalence proof exists. Component
identities, cached/reference parity and finite guest comparisons do not imply
whole-decoder equivalence or all-choice safety. The shared-ID cache partition
supersedes the earlier structural-key comparison identity; local Raw-fallback
identities do not prove the new whole-decoder implementation equivalent.
Native profiling identities preserve Lean states/outcomes, not native C compiler
correctness. The large catch guest still needs a fresh same-prepared-TyCtxt
reference comparison; native completion of a diagnostic trace does not prove UB
freedom over every permitted choice.

Import-time typing remains selective: query envelopes, layout extras and some
specialized adapters still inspect source payloads. Any prepared-input reuse
across seeds must bind input/version/configuration and create fresh guest state;
it must not reuse guest pointers or allocation identities or replace first-run
improvements. Preserve validation, context-sensitive memo keys, diagnostic
rebasing and uncached compatibility paths when extending caching.

### Shared MIR validation and callback metadata reuse

The upstream UI harness in #9 repeatedly constructed immutable compiler indices
while assembling recursive execution callbacks. Providers now retain the existing
source-bound vtable/function/inline lookup views. The root-span query outcome,
including errors, is bound to the final program; its accessor has a kernel-checked
identity with the original query. Manual provider updates must rebind affected
indices or clear the optional root-span cache.

MIR local/projection validation now reuses successful shared-node checks keyed by
(document-local node ID, local count). Terminator edges and each body's dense
indices remain checked. Failed checks retain occurrence paths; Raw fallback uses
the original traversal. Diagnostic path escaping avoids rebuilding ordinary keys;
`DecoderValues.escapePathKey_eq_reference` proves equality for every string.

Measurements use main `59f65b93` plus #9 `f7fea8dd` as the baseline, identical
untouched Rust exports, immutable native `--profile` runners, CPU 2 and one Lean
thread. Builds, exports and tests did not overlap the alternating trials. The
input/reference FNV, length and toolchain pins matched; SHA256 identities and all
15 changed source files were checked. Both runners used the reference's original
source argv[0], empty guest environment and seeded UI profile.

| Input / trial | Baseline wall / CPU / steal (seconds) | Candidate wall / CPU / steal (seconds) |
| --- | --- | --- |
| `pass/unops.rs`, 1 | 112.220 / 112.026 / 0.980 | 78.831 / 78.675 / 0.670 |
| `pass/unops.rs`, 2 | 113.845 / 113.786 / 1.480 | 78.826 / 78.721 / 0.700 |
| `pass/const-addrs.rs`, bounded prefix | 613.661 / 612.964 / 6.140 | 261.673 / 261.552 / 2.370 |
| `fail/validity/invalid_bool.rs` | 97.354 / 97.225 / 1.040 | 73.208 / 73.131 / 0.840 |

`unops` finalized exit zero in all four trials, with identical tapes, events and
terminal diagnostics. Its median wall time fell from 113.033 to 78.828 seconds
(30.26%). Peak RSS was 3.835–3.837 GB (decimal). The const-addrs pair also matched
exactly, at 4.422 GB RSS, but both stopped with `outerChoicesExhausted 100000`.
That pair measures the same **pending prefix**, not successful execution: the
reference finalized exit zero, so this case still fails the UI acceptance oracle.
The 57.36% prefix-time reduction is one pair, not a general speedup estimate.
The original invalid-bool negative case matched the independent reference UB
category and exact source line 3 in both versions, with identical tapes/events
and terminal diagnostics (3.808–3.810 GB RSS). This is one control pair.
Throttling was zero in every listed trial; steal is the raw same-CPU observation.

Validation passed: `check-quick.sh` (85 Python tests and integrity/semantic checks),
15 CI helper tests, `check-performance-regressions.sh`, independent decoder
goldens (16 + 4 shared-ID cases), and `check-structural-regressions.sh`. The
Miri/MiriTests/frontend build and axiom audit passed (70,846 declarations, only
the three permitted axioms). Cached/reference tests include changed local bounds,
malformed locals/projections, debug payloads and terminator edges.

All 300 `examples/empty_function` Lean modules also typechecked using
`tools/check-empty-function.sh` with every module selected as a root. Fourteen
proof files apply `CompilerProviders.Prepared.rootSpan_eq` at 33 factory
simplification sites. These edits only rewrite the cached query to the original
query; theorem statements, premises and the fixed Rust/MIR hashes are unchanged.
The final target type check passed. An additional combined audit of all 300
modules and their imported Miri declarations passed for 91,882 declarations,
using only propext, Quot.sound and Classical.choice.

Raw artifacts, source/binary hashes, profiles, counters and example check/audit
logs are under ignored `scratch/perf-ui/`.
Full `check.sh` and the 809-candidate upstream sweep were not run. Finishing the
long const-addrs guest under an explicit execution budget remains unresolved;
this optimization does not establish whole-machine equivalence or UB freedom.

## Feature support outside the current acceptance scope

These gaps remain in the backlog, without implying that the whole feature is
unimplemented. Check existing support against pinned upstream before extending
it; preserve implementations and fail-closed Unsupported outcomes. WP remains
deferred with its implementation removed. GenMC is removed; available race
tracking modes are disabled tracking and the Miri vector-clock backend.

* **Windows / peripheral OS facilities** —
  [WindowsPlatform](Miri/Interpreter/WindowsPlatform.lean), `MiriTests/Native/`
  and Unix tests do not guarantee every target ABI, shim or real-host connection.
  Reproduce missing capabilities with a fixed target and genuine input, then
  compare shim ABI, state and errors.
* **Native guest and math boundary** — [native](native/),
  [NativeMathHost](Miri/Input/NativeMathHost.lean), `tools/NativeRunner.lean`,
  `tools/NativeMathBoundaryQA.lean` and `MiriTests/Native/`. Signaling-NaN choices,
  other widths/exponents, f128 and broader absent-host validation remain pending.
  Existing f32/f64 exponent-zero controls use fixed results and no_std
  `miri_start`, and the f64 sin(1)/cos(0) controls cover only those absent-host
  cases. They do not establish broader numerical or std-main equivalence.
  Generate references from the same Rust and compare real-host bits and
  Unsupported outcomes; helper mocks do not resolve these gaps. Separate host
  callbacks from numerical equivalence.
* **Timezone** — [source and assumptions](docs/chrono-tz-source-port.md),
  `MiriTests/Regression/TimezoneGuestEnv.lean` and `tools/check-timezone.py`.
  General host integration, all-zone/date equivalence and timestamp
  endpoint/out-of-range behavior remain unestablished. Extend genuine
  comparisons to date-range boundaries; table generation/count checks alone
  do not resolve them. Existing finite comparisons use a separate reference
  TyCtxt with isolation disabled and a retained Linux host trace; unobserved
  host demands remain Unsupported.
