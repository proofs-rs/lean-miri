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

## Exported input coverage

Each concrete instance and promoted index has one executable MIR body. The
exporter substitutes generic arguments, normalizes types, and evaluates MIR
constants, including unused required constants, before emitting that body.
Runtime storage, pointer and layout queries use the resolved types. Unbound
generic templates are rejected as executable roots; diagnostic spans and scopes
remain attached to the resolved instructions.
The exporter aborts when requested semantic compiler data is unavailable; the
Lean input API no longer retains failed exporter payloads as execution inputs.
Successful values are serialized without success-status wrappers or a
completeness flag; consumers validate the semantic fields they use.
Compiler query catalogs and the owned final `ExportDocument` use concrete Rust
serialization types. Required vtable references finalize locally against the
closed query map;
virtual candidates are sorted and deduplicated for the exact original instance.
Pending references cannot serialize. The export document and peripheral metadata
write directly through serde without constructing a JSON Value tree. Diagnostic
fingerprints use
the emitted bytes, and prepared-reference sidecars receive the allocator frontier
directly.
Cast-query consumers, including dynamic-upcast evidence validation, read direct
result fields. Executables with custom `no_main` entry points retain startup
preflight facts and the core C-ulong and mutable i32-pointer types required by
machine construction without demanding an OS catalog. Intrinsic type-name and
caller-location constants are lowered from their direct compiler payloads. A genuine absent
function-pointer target has `resolution_kind: none` and no instance identity;
`resolution_kind: instance` carries a canonical instance ID. This preserves
the optional answer when exact query-key fields are attached.
The vtable-erasure reader uses typed predicate/type references, including
TraitVPtr child joins. Only the HRTB upcast controls require lockstep query rows;
static and cross-crate controls require direct decoding without those rows.
Resolved constants no longer retain their unevaluated definition identity, so
the cross-crate fixture checks its external constant in independently emitted
compiler MIR and checks the exported root allocation’s symbolic-vtable relocation.
This is a fixture-specific provenance check, not a general translation proof.
Local fresh wrapper checks pass for static, cross-crate, HRTB and HRTB-upcast
controls, including same-TyCtxt references, exact catalog joins over 32 salts,
and canonical Lean guest exit zero. A successful hosted rerun remains required.
Coroutine frame layout serialization and foreign TLS initializers remain
unimplemented and now stop export. This boundary does not establish compiler
query closure or interpreter correspondence.

Fifteen fixed connected inputs with their same-TyCtxt reference observations
and three eval-core inputs are regenerated under the schema-7 resolved-body
typed-pool contract. Allocation byte vectors share a document-local exact byte
image pool; function payloads group identities by Instance. Graph IDs, raw source
IDs, initialization and provenance remain independent. Prepared raw-pool slots
and indexed salt results derive serialized facts from those allocation nodes.
Span and backtrace filenames remain validated numeric IDs
in a shared exact-string file table until diagnostics or backtrace APIs present
them. Runtime-metadata checks export their
Rust inputs afresh. Performance checks now obtain
fresh producer inputs. The DST and large Tree Borrows connected cases now
generate inputs and same-TyCtxt references in CI from unchanged tracked sources,
flags and reviewed guest configuration; fixed assertions and choice tapes are
preserved. This adds pinned toolchain/sysroot build cost and replaces saved
allocation-history replay for those two cases. Their historical archives are
not CI inputs.
The 17-case Lean connected replay passes under schema 7 with unchanged expected
outcomes, including fresh same-TyCtxt references for the DST and large Tree
Borrows cases. Decoder controls reject missing byte images, repeated identities,
unmatched raw slots, incomplete salt arrays and unchecked foreign TLS
initializers. A decoded shared-byte cyclic graph retains distinct runtime IDs,
mutability, initialization and CTFE provenance flags.
The full CI matrix remains unexecuted. These finite executions do not establish
compiler query closure, interpreter correspondence or whole-machine safety.

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

The example adapter disables the new allocation-backtrace diagnostic option
through `Configuration.proofOptions`, preserving every pre-existing option.
The proof covers this legacy diagnostic-off profile; collection-enabled UI
executions are separate finite comparisons. Fixed Rust/MIR inputs and the
target theorem are unchanged.

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
coverage. Catalog-role checks now distinguish malformed typed fields from ignored
extension fields and include the optional TLS-provider branch; hosted validation
of these updated checks remains required. Saved replay cannot validate changed
producers.

The upstream UI workflow applies the requested reference and Lean settings
through explicit opt-in adapters: empty guest environment, seed zero, source
argv0, one CPU, and ordered supported runtime flags. Ordinary runner defaults
are unchanged. The uncapped seeded diagnostic policy uses SplitMix64; it does
not claim the same random stream as Miri. Strict profile and terminal oracles
retain per-field expected, observed and missing values.
The optional allocation-time collector retains full-instance/span frame traces
for allocations subject to leak checking, including MIR inline scopes and exact dummy
span fallback. UI profiles enable it unless leaks are explicitly ignored;
ordinary runner defaults keep it disabled. Eight focused unchanged upstream
sources pass the strict reference/profile/terminal oracles, including an actual
UB stop with fourteen retained allocation backtraces. Native leak-report
rendering remains Unsupported and needs implementation. This does not establish
the full UI sweep: coroutine ABI layout remains unsupported, as do Stacked
Borrows profiles, host-isolation/output-capture settings and compile-time or
nonlocal-diagnostic oracles outside the runtime profile. Export errors,
Unsupported outcomes and other interpreter mismatches remain failures. A full
successful hosted sweep and aggregate coverage remain unvalidated.

The 6aca6f0 regression run also exposed stale schema assumptions in SC schedule
validation, powi root lookup and vtable wrapper checks, and a decoder rejection
of exact JSON-natural u128 range endpoints. Local checks pass for the repaired
range boundaries, powi guest, all four vtable wrappers, and SC seeds 0–11 with
four rejected malformed logs. These finite checks require a successful hosted
rerun and do not establish whole-machine safety.
Selected finite checks do not close general proof or source-correspondence gaps.

The two-pass typed input revision passes the local library/frontend/native
build, runtime registry, decoder, fresh input, structural, optimization and
connected-proof checks. Full `tools/check.sh` and hosted CI remain unvalidated;
these finite checks do not replace the complete comparison lanes.
The full regression result for an earlier revision does not validate later
changes. Separate canonical12, ordering,
large-TB and SC-schedule entry points also need current-revision execution. Fresh construction of the reference Miri
and MIR-enabled std sysroot remains a validation gap; reusing retained artifacts
does not establish that setup path.

The ordinary standard-library startup closure from
`tests/repro/startup/empty-main.rs` now decodes directly into MIR. A fresh
7,322-body export completed native execution with `finalized_exit code=0` under
the bounded-diagnostic-zero choice profile. This finite witness does not establish
behavior for other standard-library closures or all permitted choices.

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

Remaining performance work includes residual equality and validation work,
and preparation outside typed input decoding and the optimized call-resolution
lookup. Caller-location still scans its catalog; optimization must retain
source-order diagnostics, malformed-row handling and fresh Location allocations.
Measure current immutable artifacts with the protocol in [AGENTS](AGENTS.md);
old timings and shared-host samples do not establish a general speedup.
The native harness runs until a source terminal/error outcome or process
interruption, with demand-driven diagnostic choices and no scheduler-iteration,
generated-choice-count or generated-byte-length cap. Finite proof/test APIs
retain their explicit bounds. Execution still depends on host memory and on
the interpreter's demand-local capability and operation-resource checks.

No full compiler-query/decoder equivalence proof exists. Component identities
and finite guest comparisons do not imply whole-decoder equivalence or
all-choice safety. Typed pool validation establishes bounds and selected
structural invariants; it does not prove exporter/interpreter correspondence.
Native profiling identities preserve Lean states/outcomes, not native C compiler
correctness. The large catch guest still needs a fresh same-prepared-TyCtxt
reference comparison; native completion of a diagnostic trace does not prove UB
freedom over every permitted choice.

Input decoding constructs final MIR, catalog values and per-instruction facts
while parsing concrete typed tables. Integer scalar values carry their exact
compiler byte width; the reader checks their range immediately and checks width
agreement against the completed type/layout tables. Constructor shape, local
body bounds and table identities are checked during parsing. Compact numeric
MIR-reference summaries survive until table counts are known; cross-table
references, joins and required execution graphs still require completed tables.
No duplicate MIR spine, generic JSON tree or source ranges are retained. The file
entrypoint still reads a complete `String`; bounded-memory file streaming is not
implemented. Compiler table identities remain local to one input. Reusing guest
pointers or allocation identities between executions would invalidate the
execution model.

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
