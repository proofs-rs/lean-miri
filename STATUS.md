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
The migrated proof uses production MIR IDs and checked source observations;
canonical lowered/loaded-body agreement is derived from its existing local-type
query premise. No new constant-body or caller-table premise was added. A general
old-flat-state/table-state transport theorem remains unproved, separately from
the Rust-valid-caller domain gap above. The final target and imported declaration
audit permit only `propext`, `Quot.sound` and `Classical.choice`.
Literal ID/reference facts are derived from the checked source assignment.
Constant normalization is conditional on successful evidence lookup; missing
queries are admitted checked non-UB stops. Successful intermediate results use
`SuccessfulConstant`, while the final noUB/Target premises do not require it.
`ConstantTransport` gives a local domain-inclusion encoding of successful legacy
evidence; complete old/new reader/preparation equivalence remains unproved.

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

A successful hosted regression rerun remains required after the
`MiriTests/Rvalue/Rvalue.lean` assertion elaboration fix and the hosted ripgrep
setup fix. These fixes do not establish the complete comparisons/replays or the
later exporter and fresh-input/execution phases that the failures prevented.
See [CI coverage](tools/ci/README.md) for lane commands and artifacts.

Timezone also needs a successful hosted rerun. Its CI wrapper failed before
guest execution because its libc filename glob did not identify exactly one
archive; the match count and paths were not logged. The Cargo compiler-artifact
selection fix needs hosted validation rather than relying on the old glob.

The fresh CI lane now schedules the six supplemental focused guests, native/TLS
query-demand mutations, runtime-type closure and the cross-crate vtable control;
a successful hosted run remains required. Fresh regeneration/comparison of every
canonical guest and standalone unregistered harnesses remain outside workflow
coverage. The existing CatalogRoles consumer
lacks the TLS-provider branch required by its optional generator mode.
Saved replay cannot validate changed producers.

The upstream UI workflow ports PR #9’s test harness without its compiler/runtime
fixes. Main’s reference environment and Lean choice/argv/CPU/float/CAS/I/O profile
differ from that harness’s strict contract; profile mismatches remain failures,
with attempted Lean outcomes retained. Full hosted sweep and aggregate coverage
remain unvalidated.
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

Runtime import now keeps transport references and extracts typed ID tables once.
The interpreter and compiler adapters use these checked tables. The expanding
resolver and comparison decoder live only under `MiriTests/Input`; production
has no resolver phase or alternative expansion branch. Caller-location and cast
query duplicates are compared by typed semantic fields, ignoring unrelated debug
JSON. Producer source paths retain transport-array coordinates even when typed
tables are indexed by explicit IDs.

No generic whole-reader/whole-decoder equivalence proof exists. Component
identities, the test-only expanded oracle and finite guest comparisons do not
imply exporter correctness or all-choice safety. The empty-function result and
its local conditional evidence transport are scoped above and in its README.

Performance validation uses immutable VM artifacts on one pinned CPU, fresh
exports, alternating baseline/head rounds and a shared host. Native executable
comparison remains unmeasured: the baseline native build did not complete and
storage prevented completing both binaries. An ordinary std-main pilot exceeded
the existing memory guard; it supplies no completed benchmark. Final three-sample VM medians for the two small no_std/custom-start cases were
6.656→5.982s and 8.398→7.449s (observed −10.1%/−11.3%), with peak RSS approximately
4–5% higher. These shared-host samples do not establish a general speedup;
see [protocol and results](docs/input-tables.md).

A 25MB symbolic-repeat input originally spent approximately nine minutes before
an incorrect readiness rejection. That run lacked a matching baseline and is
not a regression measurement. The source-coordinate correction has a genuine
reordered-input regression; a subsequent isolated decode-only run completed in
58.637 seconds (CPU 58.614 seconds, peak child RSS 2.09GB), with no blocking
obligations. The final-source full VM guest subsequently completed with exit 0 in 96.217
seconds (CPU 96.196 seconds, peak RSS 3.03GB), matching the independent Miri
execution's expected assertion result. Neither run has a corresponding large
baseline measurement; they establish finite completion, not a speedup claim.
Runtime-value decoding and remaining linear interners still require
representative scaling measurements.

The packed-reference negative depends on allowed address choices: equal numeric
seeds across separately prepared Lean/Miri runs do not establish identical
choice traces. A separate align(4) container puts the u32 reference at offset 1
and guarantees misalignment; both implementations reject that selected case.
These executions do not establish UB freedom over all permitted choices.

Any future prepared-input reuse across seeds must bind input/version/configuration
and create fresh guest state; it must not reuse guest pointers or allocation
identities. Preserve complete semantic query keys, checked failure paths,
context-sensitive memoization and diagnostic coordinates.

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
