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
and canonical Lean guest exit zero. These controls also passed the hosted
extended/fresh suites at `6a76fcbd`; the overall results and remaining failures
are described under Hosted regressions and coverage below.
Coroutine frame layout serialization and foreign TLS initializers remain
unimplemented and now stop export. This boundary does not establish compiler
query closure or interpreter correspondence.

The schema-9 follow-up emitted schema 9 and strictly supported schemas 8 and 9
at that revision (the later schema-10 baseline is described below).
Schema 8 retained its existing dense-layout and call-evidence validation and
rejects the new compact-array and LLVM no-ABI forms. Array offsets in schema 9
use an explicit stride/count formula instead of an enumerated vector. The
reader checks shape agreement, u64 bounds and the last offset without traversing
all fields; runtime lookup retains the existing checked multiplication. Local
theorems cover the exact offset value for every in-bounds index. Zero-length
and zero-stride arrays remain supported.

LLVM intrinsic calls carry explicit no-ABI evidence tied to the exact declared
FnDef type, DefId, generic arguments and current MIR call operand. Ordinary
calls still require genuine FnAbi evidence; no replacement ABI is fabricated.
Signature checks use the canonical prepared symbol registry and pinned builtin
exemptions, retaining missing, duplicate and weak-symbol behavior. The core call
implementation is unchanged.

Fifteen fixed connected inputs with their same-TyCtxt reference observations
and three eval-core inputs retain the schema-8 resolved-body typed-pool
contract. Allocation byte vectors share a document-local exact byte
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
The earlier hosted replay lane also passed at `6a76fcbd`. Neither result
establishes validation of the schema-9 follow-up source; the
broader hosted results and remaining failures are described below. These finite
executions do not establish compiler query closure, interpreter correspondence
or whole-machine safety.

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

At merged main `6a76fcbd2f24afaf6c0114efc205479560fb280b`, the
[Miri regression run](https://github.com/proofs-rs/lean-miri/actions/runs/43069997521)
passed the regression, fresh and replay lanes. Extended passed 21 of 22 suites;
its sole failure was the detached-join source-order check's stale whole-file
`ThreadMachine.lean` SHA after allocation initialization changed. The checked
`joinExclusive` slice is byte-identical to the prior reviewed implementation.
The local SHA refresh passes the unchanged ordering assertions; a hosted rerun
of that refresh and subsequent changes remains required.
See [CI coverage](tools/ci/README.md) for lane commands and artifacts.

Upstream main subsequently advanced through the allocation-compaction and wire
field-deduplication revisions to schema 8 at
`affc8c4128cda426557eeb5c04d273d1602917b5`. Its latest hosted runs are
[Miri regression](https://github.com/proofs-rs/lean-miri/actions/runs/43085783786),
[UI](https://github.com/proofs-rs/lean-miri/actions/runs/43085783770),
[empty-function proof](https://github.com/proofs-rs/lean-miri/actions/runs/43085783789)
and [documentation](https://github.com/proofs-rs/lean-miri/actions/runs/43085783868).
At that upstream revision, documentation build/deploy and the empty-function
proof passed, as did the fresh regression lane. Replay failed only at the stale
SC-snapshot SHA; its build, reference-profile, canonical12, ordering and large-TB
suites passed. Extended failed only at the stale detached-join file SHA. Both
pins are corrected in this follow-up, with their original checks retained.
The regression lane also failed: its constant-parser reference test added a
legacy single-identity function allocation, which schema 8 correctly rejected
before the intended dangling-instance mutation. The local fixture now uses the
schema-8 identity group and a fresh graph/source identity; the full constant
suite passes while still rejecting the legacy form and dangling instance IDs.
UI shards were still queued when checked. These upstream results do not validate
the integrated local follow-up; its completed local checks are recorded below
and a new hosted result is required.

At `6a76fcbd`, the successful hosted suites include timezone with Cargo-reported
libc archive selection, fresh producer/decoder u128 boundaries, powi and all four vtable
controls, supplemental guests, native/TLS query-demand mutations and runtime-type
closure. The replay lane includes canonical12, ordering, large-TB and SC schedules.
Pinned reference Miri and MIR-enabled standard-library setup also completed.
These results validate that revision's scheduled checks, not later producer or
interpreter changes. Fresh regeneration/comparison of every canonical guest and
standalone unregistered harnesses remain outside workflow coverage; saved replay
cannot validate changed producers.

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
the full UI sweep: coroutine frame-layout serialization remains unsupported, as do Stacked
Borrows profiles, host-isolation/output-capture settings and compile-time or
nonlocal-diagnostic oracles outside the runtime profile. Export errors,
Unsupported outcomes and other interpreter mismatches remain failures.
The [merged-main UI run](https://github.com/proofs-rs/lean-miri/actions/runs/43069997560)
completed all 32 comparison shards, each failing. Their terminal console summaries
cover 1,118 revision/profile cases: 600 passed, 309 profile-unsupported, 119 UB-kind
mismatches, 47 export failures, 22 Lean Unsupported outcomes, eight UB-site
mismatches, five timeouts, four Lean failures, three failed Lean processes and
one reference-annotation mismatch. No profile mismatch was reported. The
inventory-coverage collector subsequently confirmed `complete=true`,
`passed=false` and `expected_cases=observed_cases=1118`, with exactly these
counts. This establishes inventory coverage, not a successful UI sweep.

The earlier `6aca6f0` failures in SC schedule validation, powi root lookup,
vtable wrappers and JSON-natural u128 endpoints are covered by the successful
`6a76fcbd` hosted suites above. Local follow-up checks do not establish a new
hosted result. All local stages of `tools/check.sh` have now been exercised as
described below; a successful hosted follow-up matrix remains outstanding.
Selected finite checks do not close general proof or source-correspondence gaps.

The following local results belong to the schema-8 baseline merged in PR #44
as `54749934`. Its new hosted checks were queued when last checked; the full
hosted result for that revision is still pending.

Local baseline checks pass the concrete runtime Codegen ABI probe and 20
exporter boundary tests, including nested bound-region query views and the exact
callee ABI needed before rejecting a variadic fixed-count mismatch. Five
unchanged variadic guests, four focused diagnostic guests and four UB-kind
controls pass their strict local reference/profile/terminal oracles. This does
not provide a new hosted result. Coroutine runtime ABI queries succeed in the
probe; coroutine frame-layout serialization remains unsupported.

The shared compiler-owned `miri_start` selector passes two focused no-main
guests, but `pass/no_core.rs` still fails with `compiler named types absent`
after its matching reference exits zero. The dedicated unsized uninitialization
writer passes exact dynamic-range, permission-partial-state and zero-size checks.
After explicit tuple cast classification, the unchanged `pass/unsized.rs@tree`
guest passes a fresh same-TyCtxt reference and Lean execution with exit zero and
matching strict profiles. This is a finite local result, not a new hosted sweep.

The frozen schema-8 follow-up passes the 1,281-job library/test/native build,
46 self-contained runtime checks, the quick check with 110 Python tests, 36 Rust
unit tests, the direct runtime-ABI integration probe and the 20 producer boundary
checks. The library axiom audit covers 74,171 declarations with only `propext`,
`Quot.sound` and `Classical.choice`. SC seeds 0–11 and four malformed-log controls,
and 16 selected genuine UI cases, pass their unchanged local assertions/oracles.

For that baseline, all 66 `tools/check.sh` stages pass across resumed local runs:
stages 1–57 passed first, stage 58 passed after updating its tuple-classification test
expectation, and stages 59–66 passed after five input harnesses installed the
actual supplied allocation world through the canonical initialization path.
These were test-only corrections; Miri sources, proof sources and fixed inputs
remained unchanged. The reference exporter was restored to its recorded frozen
binary hash after the default-exporter checks.

All 268 empty-function proof roots pass on that baseline source. Its transitive
axiom audit covers 76,837 declarations using only the same three allowed axioms;
recorded Rust, input, library and proof hashes match before and after validation.
These are completed local results, not a successful full hosted matrix or a
whole-machine correspondence theorem. Hosted validation of the integrated
follow-up is still required. The no-core, full-UI and performance gaps remain
unresolved.

A separate diagnostic follow-up on `54749934` retains the reborrow cause at
the actual parent-access failure in both retag paths. A kernel-checked equality
preserves the default protector-release classification and message. The UI
oracle recognizes the exact existing `InvalidTag(outside valid range)` and
`dereferencing a null box` diagnostics; unrelated UB, access directions,
Unsupported outcomes and missing source sites remain rejected.

This follow-up passes the 1,281-job common build, 46 runtime checks, structural
regressions and the quick check with 111 Python tests. Six unchanged upstream
guests pass strict reference/profile/UB-category/site checks, covering TB
read/write/reborrow, destructor protection, enum tags and null boxes. Its library
axiom audit covers 74,172 declarations; all 268 empty-function roots and their
76,838-declaration transitive audit pass using only the same three permitted
axioms. Recorded Rust, input, library and proof hashes match before and after
validation. The 66-stage result remains specific to the baseline; this diagnostic
revision still needs full hosted validation.

At subsequent merged schema-8 main `7cc6b6cc`, the hosted empty-function proof,
documentation build/deploy and all four core lanes (fresh, replay, extended
and regression) pass. The UI sweep remains unfinished; its shard-9 AVX2
export failure used the old producer and is covered by the local repair below. These results
belong to that main revision; schema 9 has not yet received hosted validation.

### Schema-11 shared-layout test corrections

On main `62129c87`, the test-only follow-up resolves logical layout IDs through
`layouts` into `layout_values` before mutating the exact scalar/niche payload.
Decoder mutation helpers parse JSON natural values instead of calling a JSON
accessor on raw strings. The MIR fixture validator checks schema-11 locals'
exact three fields and resolves their physical layout through the type graph,
rather than requiring the removed redundant local layout field.

All 26 producer boundary tests, nine Rust integration suites and the complete
`tests/input/run.sh` pass locally. Primitive compiler/runtime ranges remain
exact: all six decimal/numeric endpoint cases pass, and all eleven malformed or
overflowing inputs remain rejected for both scalar and niche endpoints. The
schema-10 input suite also passed before rebasing. Interpreter/decoder source,
fixed Rust/MIR inputs, checksums and proof assumptions are unchanged; no release
exporter feature toggle was needed. These results repair test compatibility,
not interpreter semantics, and do not establish a new hosted result or close
the remaining gaps.

### Schema-10 UI oracle follow-up: local validation

The oracle-only follow-up on main `17330f08` changes two test/harness files.
Vtable-specific reference diagnostics take precedence over generic null-pointer
wording while uninitialized-value precedence remains intact. The calling-
convention category accepts the exact shim-convention diagnostic. The no-
provenance category recognizes only the fully qualified, case-exact typed
`Miri.Memory.AccessError.danglingIntegerPointer` constructor with a nonzero
canonical decimal address and strict namespace/integer-token boundaries.
Adjacent ABI errors, zero addresses, other namespaces, malformed address tokens,
bounds/dead-allocation/vtable errors and generic UB remain negative controls;
wrong sites and Unsupported outcomes still fail.

The latest-base quick check passes all 114 Python tests, including 19 UI-oracle
unit tests. Fresh strict comparisons pass the four repaired cases
(`invalid_wide_raw`, `check_arg_abi`, `deref-invalid-ptr` and `cast_dangling_ref`)
and two existing null-box/null-reference controls. These comparisons use sealed
schema-10 binaries from the separate Unix-allocation candidate `11c7e251`, also
based on `17330f08`: exporter SHA256 `1e0b4eb44eeddb9aa6ebdab13932c5166d773244b7f478a519e1f31471ec443a`
and native runner SHA256 `d2a20a77451114ed9881cde05d0423f7091631e3130eddeb07261fa0b0c96d9a`.
That candidate adds configured Unix allocation ownership; its vtable, foreign
ABI and memory-access cause sources have exactly the same SHA256 as this
checkout, with no terminal diagnostic changes. Source/binary identities,
same-TyCtxt snapshot bindings, strict profiles and exact source-line checks all
pass. This is a combined-candidate comparison, not a pure-main binary result.

This follow-up changes no Miri/proof source, protocol, line matching, profile,
budget or case inventory. The 268 proof roots were not rerun for these oracle
changes. The adapters identify the actual source UB causes; they do not turn
unrelated failures into accepted UB or close the remaining implementation gaps.
On hosted main `17330f08`, the proof, fresh lane and documentation build pass;
other checks are still in progress when checked. These local six-case results
do not establish a green hosted UI sweep.

### Schema-9 metadata follow-up: local validation

On the follow-up rebased onto `7cc6b6cc`, the full 1,281-job library/test/native
build, 46 runtime checks, structural regressions and decoder controls pass.
The library audit covers 74,294 declarations using only `propext`, `Quot.sound`
and `Classical.choice`. SC seeds 0–11 and four malformed-log controls pass with
their source/artifact seals. All 268 empty-function roots also pass; their
transitive audit covers 76,960 declarations with only the same allowed axioms.
Fixed Rust/MIR input bytes, SHA records, final target and caller assumptions are
unchanged, and the recorded library/proof bindings match before and after.

All 66 `tools/check.sh` stages are covered across resumed local attempts:
stages 1–50 passed before stage 51 encountered a missing vanilla-reference build
manifest in the isolated checkout. Reuse of the existing pinned vanilla Miri
build was verified against its compiler/Miri pins and binary SHA256, then stages
51–66 passed. This is neither a single uninterrupted run nor a fresh reference
toolchain setup. The reference-enabled exporter was restored to its recorded
pre-run binary SHA256 after the suite's feature toggles. After the final
Rust-only LLVM helper correction and affected checks, the reference exporter
was restored to SHA256 `5073ff656c24aa107678d4dbf8750f465d14b2978406b8669335706c20ec9c37`.
Miri sources and the fixed library/proof bindings remain unchanged.

The Rust checks pass 37 unit tests, the independent runtime-ABI integration probe,
24 producer boundary tests and nine reader checks; nine affected Rust suites
also pass. Eight focused LLVM controls cover three successful executions and
five negative outcomes with strict reference/profile/terminal checks. Unknown
Unsupported and invalid-layout rejection are not counted as guest safety
passes. Malformed identity, type, operand and ABI evidence retain rejection.
Two ordinary function-pointer/exported-symbol comparison cases and the affected
input, frontend, runtime-metadata and execution checks pass. A second route
through the ABI-synthesizing helper is now excluded only for LLVM intrinsics;
ordinary Rust helpers retain their ABI requirements and genuine query failures
remain fail-closed. The former 1-PiB offset-vector abort in the
unchanged upstream `pass/align_offset_symbolic.rs` is locally repaired: a fresh
schema-9 export completes both same-TyCtxt Miri and Lean execution with exit zero
and matching symbolic-alignment profiles, including a final fresh comparison
with exporter `5073ff65` and native runner `09ccb6b0`. A separate guest retains 1-PiB byte
and word array layouts plus `usize::MAX` zero-sized elements without allocating
those arrays; its approximately 1-MB export and both executions pass with exact
snapshot bindings under the earlier `6043755a` producer; its array implementation
is unchanged by the final LLVM-only Rust correction. Compact/dense layout boundaries, overflow and version
rejection controls pass while the fixed schema-8 example input remains intact.

These are finite local results, not a green hosted UI sweep, general query
closure proof or performance claim. All four original export-failure probes
(`intrinsic_target_feature`, SSE2, AVX2 and AES/VAES) now export successfully.
The unchanged target-feature case also passes its official strict comparison;
execution of the three long SIMD files has not been measured. Export success
does not establish their execution result. The no-core, coroutine-layout, native leak-report
rendering and performance gaps above remain unresolved.

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
At `6a76fcbd`, hosted `pass/btreemap.rs@tree` exceeded its 900-second execution
budget. A diagnostic prefix using an immutable runner from that revision with
a newer ABI-query exporter also remained unfinished at 900 seconds after
695,759 iterations. Decode took 5.44 seconds; reported slow complete iterations included
returns, reference creation and calls. This mixed-artifact, shared-host profile
does not identify an internal CPU hotspot or establish an optimization. The
execution budget and acceptance conditions are unchanged. This does not measure
the later schema-8/indexing revisions or establish their result for this guest.
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
