# Current status and remaining work

This file is the sole entry point for known remaining work. Backlog triage does
not broaden the acceptance scope, semantics, theorem claims or test expectations.
Distinguish the existence of tests and historical successes from successful
execution in the current checkout. See the
[development guide](docs/development.md#check-commands) for check entry points
and prerequisites.

## Empty-function call safety

The [empty_function example](examples/empty_function/README.md) proves `TotalCallGoal.Target` through
`ActualNoUBFinal.target` (`ActualNoUBFinal.noUB` per caller): actual call
initialization and every finite in-call execution prefix report no UB.

The target uses only `Metadata`, `Profile`, `RuntimeProfile` and
`CurrentInputDraft`. It has no numeric resource/`ChoiceFits` admission
condition, future success law or remaining family/stage proof. It observes
actual initialization and step errors with their failed states and permits
checked non-UB stops, including resource exhaustion. Normal return and
NoErrors for every resource supply are not claimed; the conditional
normal-return and eleven-clause preservation results are intermediate results.

Allocator/generator coherence for projected backing is required only when
its raw runtime and enabled-source counters are active. Zero/wrapped counters
and exhaustion flags remain admitted; when allocation is attempted, its
actual checked error is observed. Reserving the final MAX ID itself is also admitted.
`AllocatorActive` is a guard on coherence fields, not a caller premise, and
the allocator implementation is unchanged.

The current-input record explicitly describes raw caller, representation,
pointer/source, memory/borrow, address/ID and runtime coherence. A theorem
that every Rust-valid caller state satisfies this domain remains absent.
Compiler/exporter correctness and Rust/interpreter correspondence remain
trusted; the agreed pure metadata facts are explicit assumptions. The exact
race-off/shallow/fixed-scheduling profile remains in `Specification`. Other
scheduler interleavings and caller execution after return are outside scope.

Runtime definitions are unchanged; Miri additions are completed proof-only
APIs. The checker verifies fixed Rust/MIR hashes and library source stability
during validation. Proof-only reflected MIR is `noncomputable` to avoid a native-code
boxing panic, without adding axioms or replacing the interpreter.

`bash tools/check-empty-function.sh` passed on this branch: the root and its source
closure compile, the target type checks, fixed Rust/MIR hashes match, and the
transitive axiom audit permits only `propext`, `Quot.sound`, and
`Classical.choice`. `bash tools/check-quick.sh` also passed. These checks do
not establish compiler/exporter correctness or the missing caller-domain
transport theorem.

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

### Automated regression scope

Run [40192012725](https://github.com/proofs-rs/lean-miri/actions/runs/40192012725)
on `3d55eace` stopped the broad regression suite at
`tests/memory_state/run_lifecycle_differential.sh` because the hosted runner
lacked `rg` (ripgrep). Later phases of `check.sh`, including exporter and fresh
input/execution comparisons, were not executed in that lane. Explicit dependency
installation and an early setup check address the infrastructure defect; a new
successful run is still required to establish those results.

The Miri regression workflow selects the existing broad regression checks,
additional component comparisons, saved connected/ordering/SC/large-TB replay,
and fresh math/timezone/vtable identity controls. Its commands and result format
are documented in [CI coverage](tools/ci/README.md). Adding the workflow is not a
record of a successful run; use each commit's Actions results and artifacts.
Fresh regeneration/comparison of every canonical and focused guest, the complete
argument-driven query-demand suite, and standalone unregistered harnesses are
not yet covered by this workflow. Saved replay cannot validate changed producer
behavior. The selected finite checks do not close the general proof or source
correspondence gaps below.

In run [40192012725](https://github.com/proofs-rs/lean-miri/actions/runs/40192012725),
21 of 22 extended suites passed, but timezone stopped before guest execution
because the CI wrapper's libc filename glob did not identify exactly one archive.
The number and paths of those glob matches were not logged. Record and consume
Cargo's actual compiler-artifact path rather than assuming the output layout;
a successful timezone rerun is still required. This failure is not a guest
behavior comparison result.


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

### Runtime-value structural-hash reuse

The first optimization carried the existing validated
[JsonTraversalCache](Miri/Input/JsonTraversalCache.lean) nodes through runtime-value
array and object children. Its key reused the structural hash while retaining
full JSON equality, decoding context flags and per-occurrence diagnostic rebasing.
A kernel-checked comparison identity related that key to the original full-value
key. The shared-node changes below supersede that key; the uncached reference
decoder remains available. This was not a general decoder equivalence proof.

The native [decode-only profiler](tools/ProfileRuntimeDecoder.lean) separates JSON
parsing from runtime-value decoding without executing the guest. Two alternating
candidate/baseline pairs used the retained 31,718,745-byte large-TB input, frozen
native binaries, CPU2 and one Lean thread. All passed strict decode readiness.

| Trial | Baseline wall / CPU / steal (seconds) | Candidate wall / CPU / steal (seconds) |
| --- | --- | --- |
| 1 | 47.588 / 46.790 / 31.200 | 32.280 / 32.181 / 18.760 |
| 2 | 25.677 / 25.603 / 10.800 | 24.658 / 24.600 / 11.850 |

The internal runtime-value spans were 8.86/9.52 seconds baseline and 5.33/4.56
seconds candidate. Other phases varied substantially, and baseline trial1 had
1.048 seconds of cgroup throttling (the other three had none). These shared-host
samples do not establish a small whole-decoder speedup. Steal is the raw
same-CPU observation, not process CPU time. Sampled peak process-group RSS rose
from 475–476 MB to 526–529 MB; retaining traversal nodes through runtime-value
decoding extends the cache lifetime. The small input passed readiness in both
versions, with 2.963/2.584 seconds baseline/candidate wall time; this is one pair.

JSON parsing took 0.883–1.06 seconds in the four large trials. Replacing the wire
encoding alone therefore targets a small fraction of this input's measured cost.
This motivated the shared-node and typed-metadata work described below. The
external format remains JSON; retaining document-local node IDs internally and
including decoding context in memo keys removes further structural work without
a format migration. Validation and diagnostic rebasing remain required.

Validation: `tools/check-performance-regressions.sh` passed, including native
cached/reference comparisons of readiness, ordered obligations and ABI/body
payloads, shared/inline duplicates, context changes and rebased escaped paths.
Its axiom audit passed 69,676 declarations using only the three permitted axioms.
The independent decoder goldens passed 16 cases plus 4 shared-ID cases natively;
quick checks passed all 70 Python tests plus source/audit/fixture checks. Native
profiling and parity targets built successfully. Earlier VM golden/parity
attempts were interrupted and the same assertions completed natively. The
initial stale-module regression invocation was corrected; all attempted logs
are retained. At this stage, full `check.sh`, fresh producer/Miri comparisons and
whole-guest timings had not been run; the large-input follow-up is below.
The tested implementation, harness, build and toolchain
files were hash-checked unchanged after integrating the concurrent CI changes
from main. Frozen artifacts, hashes, raw counters and internal profiles are in
ignored `scratch/runtime-value-cache/`.

### Large catch-panic measurement follow-up

The same [catch guest](tests/repro/unwind/catch_guest.rs) was freshly exported
with the pinned compiler, `LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1`, `--root main`
and crate name `catch_guest`. The schema3/shared-payload-v2 input is 278,817,280
bytes, 736 bytes smaller than the historical 278,818,016-byte artifact. Its SHA256
is `005614751be65ee4c8f0d1571bfd323fec262a537e481afedff1e22ca5027821`;
it is a re-export of the same source, not the historical byte-identical input.
It contains 1 selected body, 9,991 instances, 26,625 types, 180,133 allocations,
43,827 caller-location rows and 1,574,011 shared nodes.

Frozen full native runners shared all harness/dependency objects; only the
Decoder object was replaced with the pre-change source from `21f163b1`, using
the same Lean package/module setup and C compiler flags. Generated consumers
call the decoder entry point and contain none of the changed private runtime-
value implementation symbols. The small control matched terminal/tape/events
before the large trials. Builds and exports were excluded from timing and did
not overlap the four sequential baseline/candidate/baseline/candidate runs on
CPU2 with one Lean thread, `--profile` and the unchanged no-seed diagnostic policy.

| Trial | Baseline wall / CPU / steal (seconds) | Candidate wall / CPU / steal (seconds) |
| --- | --- | --- |
| 1 | 641.527 / 635.650 / 333.180 | 573.440 / 568.635 / 295.350 |
| 2 | 665.373 / 650.205 / 362.950 | 527.109 / 520.578 / 259.370 |

| Metric | Baseline | Candidate |
| --- | ---: | ---: |
| Full process wall median (seconds) | 653.450 | 550.274 |
| Read/decode wall median (seconds) | 302.814 | 212.698 |
| Internal runtime-value median (seconds) | 103.850 | 42.600 |
| Internal JSON parse median (seconds) | 9.430 | 11.045 |
| Sampled peak process-group RSS (GB, decimal) | 3.338–3.354 | 3.849 |

The observed whole-process median difference is 103.176 seconds. Runtime-value
spans were 95.7/112.0 seconds baseline and 42.4/42.8 seconds candidate. Unchanged
phases also varied; do not attribute the entire whole-process difference to this
change or infer a precise general speedup from these two shared-host pairs.
Baseline trial2 had 9.231 seconds of cgroup throttling; the other trials had
0.002/0.068/0.079 seconds. Steal is recorded raw, without a CPU-time correction.
These values must not be compared directly with the historical 205-second run.

All four runs passed strict readiness and finalized exit0/cursor2640, with
byte-identical consumed tapes, choice events and terminal output. All leak walks
reported live39/root22/edges17. Input and frozen binary hashes remained unchanged
afterward. This is finite execution evidence, not safety over all choices or
a new same-prepared-TyCtxt comparison with reference Miri.

Preparation attempts remain visible: the previously cached debug exporter emitted
schema2 and was not measured; a schema3 unscoped export was rejected at readiness
with 9,247 blocking obligations and is not counted as successful execution. The
corrected export selects main, retaining runtime checks for demanded queries.
Raw artifacts, compiler/link manifests, all attempted logs, per-run counters and
the structured `results.json` are in ignored `scratch/catch-runtime-value/`.

### Node identities and import-time compiler metadata

The traversal builder now retains the exporter's existing document-local node
IDs and reference edges. Repeated shared references keep the same identity;
inline values are traversed directly, without new IDs or independent memo
entries. Runtime-value memoization and successful validation visits compare
shared IDs plus the existing context flags, avoiding structural JSON comparisons.
Scalars are decoded directly, including shared scalar strings.
Structural keys remain for the public FnAbi sequence's value-based deduplication.
Noncanonical manually constructed JSON still uses the uncached fallback. No
additional Lean interning or external encoding change is introduced.

FnAbi queries are decoded into an immutable typed table during import, reusing
the already prepared layout memo. Its private constructor binds all entries to
the exact shared-node table and decoder build. Query failures are stored, not
raised for unused catalog entries. Preparation consumes these typed outcomes
and still converts/validates the physical ABI against the current runtime.
Manual documents without the table retain the original path. Source-node table
updates cannot silently reuse a table indexed by the old source array. Call-site
lookup uses one index over the typed ABI records instead of scanning their JSON
payloads for every call. Noncanonical manual values keep the original linear
lookup and first-match behavior.

Complete compiler values for generic arguments and source spans are also
prepared once from shared nodes and reused by instance, scope, lifecycle,
backtrace, main, constant and intrinsic adapters. Their memo stores exact JSON
keys and full typed values rather than the runtime decoder's shallow summaries;
missing keys decode directly, and malformed raw keys bypass memo lookup.
This is selective import-time typing, not elimination of every JSON field read:
query envelopes, layout extras and several specialized adapters still inspect
source payloads. Guest pointers, allocation identity and fresh guest state are
not memoized.

To carry the checked projections in the document without a circular import,
model node definitions moved to `Miri/Input/Model/Types.lean`, value decoders to
`Miri/Input/DecoderValues.lean`, and document/validation entrypoints remain in
`Model.lean`/`Decoder.lean`. Existing public decoder names remain available.
The caches belong only to native runtime `ImportDocumentCore` values. Diagnostic
and reflected `ImportDocument` values retain their original schema fields;
conversion from those values uses the uncached compatibility path. Frontend
reflection still emits typed constructor data, without quoting private caches
or inserting an opaque decoder call. Temporary decode memos are existential
proof witnesses and are erased rather than retained in the document.
The earlier structural-key equality lemma describes the initial hash-only
implementation; ID-based memoization has a different cache partition and does
not claim that key-comparison identity or whole-decoder equivalence. New local
kernel-checked identities preserve both the old full-value key comparison and
hash exactly in the uncached Raw fallback.

Validation on source revision `267f46a09b67e0c0e4fe2fa57243fc127f44d589`:
`tools/check-performance-regressions.sh` passed, including the native build,
frontend reflection, cached/reference diagnostics and obligation ordering,
compiler ABI/value comparisons, runtime ABI rejection checks and the transitive
axiom audit (69,823 Miri declarations; only the three allowed axioms).
`tools/check-quick.sh` passed all 70 Python tests. Selected LowerContext,
ProviderContext and PrimitiveRebinding structural checks also passed. A small
native control matched the complete tape, choice events and terminal result.
The full `check.sh`, full miri_tests runtime registry and a fresh same-TyCtxt
reference-Miri comparison have not been rerun for this revision.

The combined change was measured against the previous hash-only PR head
`77f60e8489f0152d2b33eb00af36f7bddb29e942`, with candidate source
`267f46a09b67e0c0e4fe2fa57243fc127f44d589`. Two alternating sequential pairs
used CPU2, one Lean thread, native `--profile` runners, and the same immutable
278,817,280-byte schema3 catch input as the preceding experiment (SHA256
`005614751be65ee4c8f0d1571bfd323fec262a537e481afedff1e22ca5027821`).
No export, compilation or tests overlapped these timed trials. Runner hashes:
baseline `594bdde92fd2536a3833022c5276c2074cd4c293c36cd2a195a4fc39f9d59305`,
candidate `029043353625bfc08555c711d065952be2793a473f0cf4f54fc7e2d0cdd29f98`.
Input, runner and candidate source hashes were checked before and after.

| Metric | Previous hash-only head | Shared IDs + typed metadata |
| --- | ---: | ---: |
| Whole-process wall, trials (s) | 365.478 / 372.885 | 274.444 / 278.184 |
| Whole-process wall median (s) | 369.181 | 276.314 |
| Process CPU, trials (s) | 360.993 / 371.207 | 272.981 / 276.577 |
| Same-CPU steal delta, trials (s) | 127.25 / 131.83 | 79.95 / 80.19 |
| Cgroup throttling delta, trials (s) | 9.202939 / 0.026710 | 0.000021 / 0.818928 |
| Sampled peak RSS (decimal GB) | 3.849–3.850 | 3.848 |
| Read/decode wall median (s) | 157.649 | 125.394 |
| Preparation wall median (s) | 80.989 | 37.257 |
| Combined read/decode + preparation (s) | 238.638 | 162.652 |
| Runtime-value internal span median (s) | 26.100 | 22.700 |
| Call-resolution internal span median (s) | 37.850 | 0.865 |

The observed whole-process median reduction is 92.867 seconds (25.15%, about
1.34 times throughput for this case). These are shared-host observations from
two pairs, not a precise general speedup guarantee or attribution of every saved
second. Unchanged guest execution also varied (median 103.906 to 90.225 seconds,
including bootstrap), and the first baseline's cgroup throttling was substantial.
The body-validation span varied 52.2/20.9 seconds before versus 16.7/18.1 after.
Import-time typing moves some work out of preparation: candidate FnAbi query
and compiler-value preparation spans had medians 0.742/3.215 seconds. Compare
whole-process or combined decoding/preparation rather than preparation alone.
JSON parsing medians were 5.675/6.385 seconds, so replacing the wire encoding
alone still addresses little of this measured runtime.

All four trials passed strict readiness with zero obligations and finalized
exit0/cursor2640, with byte-identical consumed tapes, choice events and terminal
output. All leak walks reported live39/roots22/edges17. This is one bounded
execution comparison, not all-choice safety or whole-machine equivalence.
The first attempted baseline reached the 1,200-second timeout during guest
execution and is excluded from completed samples; its JSON parse alone took
50.9 seconds. The successful retry used a 3,600-second limit per run. The earlier
approximately 550-second hash-only median came from a different host interval
and is not the baseline for this comparison. Raw logs, including the timed-out
attempt, counters, results and immutable manifests remain in ignored
`scratch/node-id-typed/`.

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
Full `check.sh` and the 809-candidate upstream sweep were not run. At that checkpoint the
long const-addrs guest remained unresolved; the subsequent native-driver results
below supersede that blocker. Neither optimization establishes whole-machine
equivalence or UB freedom.


### Further compiler reuse and native execution without implicit quotas

Allocation-world validation is computed once by the native decoder and bound
by type to its exact raw JSON, typed allocation rows and compiler world. The
getter's equality with the strict validator is kernel checked; failures remain
deferred to their original demand sites. TLS rows likewise reuse the exact
ordered scan, with whole-query equality proofs preserving duplicates and errors.
Recursive configurations also reuse existing symbol and inline lookup indices.
Optional JSON queries avoid discarded error strings, with proved equality.
Singleton reference checks inspect actual tree shape, including malformed Raw
size annotations. MIR consistency checks use Lean's proof-guarded `withPtrEq`
fast path with complete structural comparison otherwise; `bodyContentsEqual_eq`
is definitionally exact. A broader field/path cache was rejected: negligible
wall-time benefit and approximately 600 MB extra RSS on unops.

Pinned Miri's `concurrency/scheduler.rs::run_threads` and ui_test 0.30.7 have no
matching 100,000-iteration or generated-choice/byte quotas. NativeRunner now
repeats the fixed RunLoop iteration until actual termination/error, without a
preallocated outer choice list. `--max-iterations N` remains an explicit pending
prefix limit. Existing finite proof APIs keep their original bounded behavior.
Native diagnostics keep the same zero/seeded algorithms, supplied-prefix
validation and full replay history, without the implicit 65,536-draw/4,096-byte
quotas. This does not assert rand/Miri RNG equivalence or safety of other traces.

The UI harness no longer defaults to a 600-second Lean timeout or 15.5 GB memory
guard; `--timeout` and `--memory-limit` opt into host resource controls. Killed and
pending runs still fail comparison. Export/build budgets and the GitHub job
deadline remain infrastructure controls. Component recursion/query budgets and
unavailable host services remain support limits; this is not full Miri equivalence.

The unchanged original const-addrs input (EVALS=64, inline MIR disabled) now
finalizes exit zero: 309.129 wall / 309.053 CPU seconds, 74,057 choices, 4.423 GB
RSS, 2.420 seconds same-CPU steal and zero throttling. Both old native quotas are
exceeded. This is one full-run observation; the old binary cannot supply a
full-run timing because it stops pending at 100,000 iterations.

Additional timings compare the preceding optimized native binary (`b6390f6a`)
with runtime source `a9f2789e` (`700a8d0a` binary), not the original pre-optimization
baseline. Inputs are byte-identical original exports. Trials alternate candidate
and baseline sequentially on CPU 2 with LEAN_NUM_THREADS=1; builds and tests do
not overlap. Wall/CPU/steal are raw seconds; throttle deltas are zero throughout.

| Input / trial | Previous wall / CPU / steal | New wall / CPU / steal |
| --- | --- | --- |
| unops, 1 | 76.171 / 75.645 / 0.800 | 57.808 / 57.667 / 0.450 |
| unops, 2 | 76.290 / 76.154 / 0.700 | 57.190 / 57.147 / 0.580 |
| const-addrs, 100,000-iteration prefix, 1 | 252.872 / 252.548 / 2.940 | 114.655 / 114.509 / 1.300 |
| const-addrs, same prefix, 2 | 248.717 / 248.426 / 1.930 | 114.571 / 114.516 / 0.920 |
| invalid-bool, 1 | 69.856 / 69.772 / 0.590 | 53.767 / 53.655 / 0.410 |

Unops median falls 76.231 → 57.499 seconds (24.57%); the half-time target is
still unmet for this input, whose decoder/preparation work dominates. Const-addrs
prefix median falls 250.795 → 114.613 seconds (54.30%), meeting that target for
the same prefix, not for full execution. Candidate/base ranges are respectively
57.190–57.808 / 76.171–76.290 for unops and 114.571–114.655 /
248.717–252.872 for the const prefix. Peak RSS remains about 3.84 / 4.42 GB.
Full tapes, events and terminal observations match exactly between old/new runs
of each input/prefix. The independent pinned reference oracle accepts unops and
the full const run, and invalid-bool at its original source line 3 (invalidBool 2).
The invalid-bool pair is a single control observation, not a spread estimate.
Both const prefix results remain pending, never passing outcomes. The full-run
result above is separate. Native FNV/length, SHA256 and compiler pins match the
retained reference bindings. Raw profiles, counters, manifests, input/reference bindings,
parity results and example audits are under ignored scratch/perf-next/.

Validation passed: quick/integrity checks (88 Python tests), 18 guard/UI helper
tests, 15 CI helper tests, native runner regressions, performance/structural regressions and connected
component proof checks. The full MiriTests build passed; existing rvalue runtime
assertions needed explicit IO Unit elaboration, with assertions retained. The
Miri audit passed for 71,056 declarations. All 300 empty-function modules compiled;
index/Bernoulli non-UB proofs include the new unbounded-policy cases. The final
NoUB target type/premises and Rust/MIR hashes are unchanged. The combined audit
passed for 92,058 declarations, using only the permitted three axioms. The unused
example remaining-quota helper now returns Option Nat, with none for unbounded.
The full upstream inventory has not been rerun by these focused checks.

### Checked graph summaries and canonical span indices

The importer now computes conservative subtree classes during its existing
bottom-up graph/hash preparation. ABI, body, reference and vtable-cast scans
skip only branches containing none of their relevant fields. The complete
runtime obligation scan, readiness gates and demand-time errors remain in place.
Visited exporter IDs use a byte array; raw/noncanonical input and out-of-range
internal keys retain the original exact-key set fallback.

`LEAN_MIRI_PREPARED_SCAN_FLAGS=1` optionally lets the exporter emit the same
per-node summaries while interning its graph. Lean recomputes and checks every
summary before pruning, including summaries of unused nodes. Incorrect bits,
lengths and unsupported values fail closed. Legacy exports remain supported,
and the default wire output is unchanged. This is checked preparation metadata,
not a switch to a binary format or a transfer of interpreter execution to Rust.
JSON text parsing alone is about 1.9 seconds in the cold unops run.

Compiler providers also prepare a span index tied by type to their final span
array. `CompilerSpanLookup.Prepared.find_eq` and `findUsing_eq` prove equality
with the original first full-equality list lookup for every array and query.
Hash buckets use numeric bounds, while complete payload, filename, hygiene and
source coordinates decide equality; collisions, duplicates and missing spans
retain their original behavior. Manual providers can omit the index. The
existing local-span theorem keeps its original premises and conclusion.
A source-span-only wire/memo prototype showed no clear speedup and was removed.

Final native artifacts compare the immediately preceding span-search candidate
(`0f9ad346`), rather than the much older pre-optimization interpreter, with
`7fb2fa62`. The three original exports are byte-identical throughout these
trials. Each final pair runs sequentially on CPU 2 with one Lean thread, without
builds or tests in the measurement interval. Raw seconds follow; throttling is
zero in every trial. These final pairs each have n=1, so no spread estimate is
claimed for the final artifact. Earlier frozen traversal-only trials separately
repeated unops at 45.693/45.706 seconds against 55.946/55.012 seconds.

| Full input | Previous wall / CPU / steal | New wall / CPU / steal |
| --- | --- | --- |
| unops | 54.541 / 54.525 / 0.210 | 45.471 / 45.417 / 0.430 |
| const-addrs, original EVALS=64 | 148.447 / 148.321 / 1.510 | 114.424 / 114.390 / 0.660 |
| invalid-bool | 54.805 / 54.690 / 0.340 | 43.707 / 43.565 / 0.260 |

Observed wall reductions are 16.63%, 22.92% and 20.25%. Peak RSS changes from
3.84/4.42/3.81 GB to 3.91/4.51/3.88 GB respectively. All positive inputs finalize
exit zero; const-addrs consumes all 74,057 choices. Invalid-bool still reports
invalidBool 2 at original source line 3. Full consumed tapes, choice events and
terminal observations match exactly between each baseline/candidate pair.
Independent pinned Miri references, native FNV/byte lengths and SHA256 bindings
are checked. This does not meet the further half-time target.

A separate fresh-source pipeline pair uses the identical original unops Rust
source, rustc arguments and pinned tools, with seed 0 and an empty environment
for each same-TyCtxt reference. The previous exporter is rebuilt from `330a5b59`;
the new exporter enables the optional summaries. Each fresh export has its own
unaltered fingerprint-bound reference. Compiler query row ordering can differ
between fresh exports; this is a source-to-result comparison, not an assertion
that those two MIR files are byte-identical. Tapes/events/terminal results match
exactly, and each independent oracle accepts the completed execution.

| Pipeline phase | Previous wall / CPU / steal | New wall / CPU / steal |
| --- | --- | --- |
| export plus prepared Miri reference | 79.414 / 79.221 / 1.700 | 75.068 / 74.973 / 0.280 |
| native execution | 54.817 / 54.718 / 0.510 | 45.698 / 45.508 / 0.210 |

The phase-wall sum is 134.231 → 120.766 seconds; total measured pipeline wall,
including collection/fingerprint overhead, is 134.536 → 121.085 seconds. All
throttling deltas are zero. Exporter peak RSS is 9.81 → 9.86 GB. This is one
pipeline pair, with no spread estimate and no separate claim that the small
exporter timing difference is caused by summaries. An exploratory trial with a
mismatched reference profile was rejected and excluded from these results.

Validation passed: performance regressions and full MiriTests typechecking,
native runner tests, cached/reference decoder parity, structural regressions,
88 quick/integrity tests, eight Python wire tests and six Rust sharing tests.
The Miri axiom audit covers 71,161 declarations. All 300 empty-function modules
compile without example source edits; the original Rust/MIR hashes and final
NoUB target type/premises are unchanged. Their combined audit covers 92,163
declarations and admits only propext, Quot.sound and Classical.choice.

The half-time goal remains open. Generic runtime-value decoding/preparation and
repeated full-instance body lookup remain substantial costs. No generic binary
serializer is claimed to solve those costs. The full 809-candidate upstream
sweep has not been rerun. Frozen binaries, raw counters, profiles, equality/oracle
checks and combined example audits are retained under ignored
`scratch/perf-prepared/`.

### Persistent exporter construction

The exporter now constructs an immutable shared graph instead of cloning
expanded `serde_json::Value` trees. The `json!` construction adapter retains
payload nodes directly, mutations copy only changed containers, and vtable
metadata patches visit shared nodes once. Final encoding memoizes shared source
nodes by identity and field role; unique nodes need no retained snapshot.
Structural wire keys compare complete ordered contents (including numeric
spelling), so hash collisions cannot merge distinct compiler/runtime identities.
The compact final catalog is serialized directly, without subtree string keys.
Compiler query demand/order, root schema 3 / shared-payload schema 2, and checked
prepared scan flags retain their previous behavior. The old builder/encoder is
available through the comparison-only `legacy-json` Cargo feature.

Validation on this change: 13 Rust unit tests, all nine exporter integration
entry points (Python wire tests, four fixture scripts and four producer checks),
eight legacy-builder Rust tests, the ordinary pinned Cargo check, and quick
source/integrity checks (88 Python tests) passed.
Tests compare exact bytes with the prior encoder across generated fixtures,
retain copy-on-write snapshots, force structural hash collisions, preserve exact
and unknown vtable query links, and construct 40 levels of doubled payloads
without exponential expansion. Fresh original `unops.rs` exports replay to exit
zero with exactly matching full tapes/events/terminal results against the old
exporter. Each input has its own pinned, fingerprint-bound Miri reference.
Fresh `invalid_bool.rs` retains invalidBool 2 at original line 3; its expected
Miri UB diagnostic and annotation are checked independently of process exit.
Lean runtime/example sources and saved fixture inputs are unchanged; their
full proof/axiom checks were not rerun for this exporter-only change.

Two final old→new paired export/reference trials use the same original
`pass/unops.rs`, rustc flags, CPU 2, one Lean thread, seed 0 and empty guest
environment, sequentially with no overlapping builds/tests. Old exporter SHA256
is `f3e5dab13aac15348dfda3509d8b1a01812bfda36847701be22ffd184e4c8eba`;
new is `3f30b411701272dbe8cd7fbf0740947d634bee12edb1243068e703114244f100`.
The unchanged native runner remains `7fb2fa62` from the preceding measurements.

| Export + same-TyCtxt Miri reference | Old | Persistent construction |
| --- | ---: | ---: |
| Wall, seconds (two samples) | 76.094 / 78.345 | 43.684 / 44.107 |
| CPU, seconds | 75.873 / 78.115 | 43.525 / 43.974 |
| Peak sampled process-group RSS, decimal GB | 9.864 / 9.864 | 4.930 / 4.936 |
| Selected-CPU steal, seconds | 0.35 / 0.81 | 0.31 / 0.29 |

Cgroup CPU throttling deltas are zero. Mean preparation wall time falls about
43%, and peak RSS about 50%, in these shared-host observations. An additional
candidate-only observation is 43.471 seconds; the earlier 59.815-second prototype
predates the unique-node memo fix and is excluded from the final comparison.
One full fresh-source pair measures 121.341→88.711 seconds including native
execution (44.901→44.724 seconds); the preparation change does not establish a
native interpreter speedup. Fresh compiler query row ordering can differ, so
large snapshots are checked against their own references rather than assumed
byte-identical. Exact wire bytes are compared by the isolated encoder tests.

The further half-time goal and full 809-candidate sweep remain open. This change
reduces exporter preparation; generic Lean decoding and guest execution remain.
Raw counters, artifact/source hashes, reference bindings and validation output
are under ignored `scratch/perf-direct-dag/`.

### Pipeline bottleneck attribution after persistent construction

`LEAN_MIRI_PROFILE_EXPORT=1` now emits optional adjacent wall spans without
changing compiler queries. Covariance subspans are nested in their outer phase
and are excluded when summing outer exporter spans. See `tools/PROFILING.md`.
No optimization is claimed by this diagnostic-only change.

On the unchanged original `pass/unops.rs`, two detailed exporter/reference runs
are 43.688 / 44.080 seconds (CPU 43.524 / 43.919; RSS 4.931 / 4.931 GB; selected
CPU steal 0.26 / 0.37 seconds; zero throttling). The principal outer spans are:

| Exporter/reference phase | Seconds, two detailed trials |
| --- | ---: |
| Covariance catalog | 15.667 / 15.853 |
| Final structural sharing | 9.595 / 9.703 |
| Vtable patches | 2.625 / 2.660 |
| Scope/catalog obligations | 2.528 / 2.550 |
| Destruction of snapshot graph | 2.843 / 2.821 |
| JSON file write | 1.740 / 1.738 |
| Actual prepared Miri reference execution | 0.084 / 0.085 |

A further covariance subprofile attributes 14.867 seconds to debug-string-key
sorting/deduplication, versus 0.292 seconds constructing its result rows and
0.017 seconds normalizing groups. The closure takes seven rounds; the final
round has 17,273 normalized groups and 32,553 pairs before / 32,478 after dedup.
`sort_by_key` repeatedly formats both deep types during comparisons; this is
not primarily the actual rustc relation query. Caching sort keys and avoiding re-sorting unchanged pairs
was the first local optimization candidate; the later measurements below
implement it.

Native measurements use the same frozen `7fb2fa62` runner and unchanged
fingerprint-bound input from the preceding exporter change, CPU 2 and one Lean
thread. Two unops trials finish in 46.197 / 44.420 seconds (CPU 46.171 / 44.372;
steal 0.53 / 0.33 seconds; zero throttling). Parent-observed phase boundaries,
rather than sums of potentially nested profiler spans, give:

| Native unops phase | Seconds, two trials |
| --- | ---: |
| Read/strict decode | 26.708 / 25.452 |
| Lower MIR | 4.596 / 4.334 |
| Prepare providers/runtime input | 10.647 / 10.480 |
| Bootstrap | 1.428 / 1.387 |
| Post-bootstrap interpretation to raw result | 0.837 / 0.847 |
| Exit finalization | 0.004 / 0.004 |

One original `const-addrs` EVALS=64 control finishes exit zero with 74,057 choices
in 122.393 seconds: decode 36.638, lowering 5.652, preparation 12.762, bootstrap
1.528 and post-bootstrap execution 61.766 seconds (CPU 121.629, steal 1.10;
zero throttling). This is a single attribution run, not a performance spread or
an end-to-end const export measurement. Its guest cost differs substantially
from unops. Slow-iteration spans cover only 0.669 seconds of those 61.766;
sub-10ms repeated operations still need attribution. Full-instance/body checks
in `CompilerFrameContext.bodyOfFrame`/`CallResolution.loadedBodyOfInstance`
perform repeated exact instance/source scans and are a candidate, not a measured
fraction of that execution time.

The next half-time objective applies to the full approximately 89-second unops
pipeline. Optimizing its interpreter loop alone cannot deliver it. First remove
repeated covariance sorting; then investigate construction-time canonical node
IDs and checked prepared MIR/compiler tables, avoiding final global interning
and generic JSON → typed model → lowered MIR → runtime projection passes.
JSON text parsing alone remains around two seconds. An ABI-only transport
change has too narrow a scope. A prepared format must retain exact identities,
unsupported/unknown outcomes and independent validation of references, compiler
metadata and obligations; no checks may be replaced by trusting a readiness bit.
Exporter around 20 seconds plus native around 20–24 seconds is a design target,
not a benchmark result. A general half-time claim for long-running guests also
requires execution-hotspot work. The full UI sweep remains unrerun.
Validation: 13 exporter Rust unit tests and quick/integrity checks (88 Python
tests) passed. Five instrumented exports have independently verified pinned
references/fingerprints. Both fixed-input unops replays, a fresh instrumented
unops replay and the original const control retain exact complete tapes, events
and terminal output against their preceding frozen-runner observations.
Raw profiles, counters, frozen artifacts and source/reference bindings are in
ignored `scratch/perf-bottleneck/`.

### Cached covariance ordering

The covariance exporter now caches each immutable compiler type's debug string
within one `ExportContext`. A stable cached-key sort formats each key once;
known pairs reuse integer ranks from the previous textual ordering. Equal debug
keys share a rank, preserving incoming tie order and the original adjacent
pair deduplication. New keys rebuild the entire rank domain to prevent stale
ranks after insertions/removals. The pair domain, compiler relation calls,
result rows and subsequent type-ID sort are unchanged. No relation answers,
unsupported outcomes or compiler demands are cached or skipped.

A separate `LEAN_MIRI_VERIFY_COVARIANCE_SORT=1` original-unops export compares
the complete pre-dedup pair sequence with the old sort in the very same TyCtxt
in all seven rounds. It passes, including reuse on the last round. This
43.730-second oracle run deliberately performs both sorts and is excluded
from performance trials. Two unit tests cover changing domains, subsets,
insertions, duplicate pairs and distinct identities with equal textual keys,
including 100 generated waves compared with the prior stable sort.

Final measurements use frozen old/new exporters, identical original unops
source/rustc flags, CPU 2, one Lean thread, seed 0 and empty guest environment.
Trials are sequential old→new twice, without overlapping builds/tests.

| Export + same-TyCtxt Miri reference | Old | Cached ordering |
| --- | ---: | ---: |
| Wall, seconds | 42.795 / 42.601 | 27.338 / 27.334 |
| CPU, seconds | 42.627 / 42.573 | 27.189 / 27.286 |
| Peak sampled process-group RSS, decimal GB | 4.931 / 4.931 | 4.931 / 4.931 |
| Selected CPU steal, seconds | 0.34 / 0.27 | 0.15 / 0.21 |
| Debug sort/dedup, seconds | 14.820 / 14.765 | 0.048 / 0.050 |
| Complete covariance catalog, seconds | 15.220 / 15.168 | 0.425 / 0.435 |

Cgroup CPU throttling deltas are zero. Mean export/reference wall time falls
about 36% in these shared-host observations. The first pair also runs the
unchanged native executable on each fresh export: 45.601→44.599 seconds, with
no native interpreter speedup claimed. Export+execution phase sums are
88.396→71.937 seconds, about 19% shorter in this single full-pipeline pair.
Full tapes, choice events and terminal observations agree exactly, ending
exit zero. Every timed export and the oracle export have independent pinned,
fingerprint-bound references; original source and artifact hashes are recorded
in ignored `scratch/perf-covariance/` with raw wall/CPU/RSS/steal/throttle data.

Validation passed: 15 Rust unit tests, all nine exporter integration entry
points, ordinary pinned Cargo check and quick/integrity checks (88 Python
tests). Lean runtime/example sources, JSON schema and saved fixtures are
unchanged; no full Lean proof/axiom audit or 809-candidate UI sweep was rerun.
The full-pipeline half-time goal remains open. Final structural sharing and
Lean decoding/lowering/preparation are the remaining common bottlenecks.

### Remaining unops costs after covariance sorting

Further attribution uses the same frozen cached-order exporter and native
`7fb2fa62`, original unops source and unchanged fingerprint-bound input.
No Rust/Lean interpreter/exporter behavior changes are made in this investigation.
Optional `tools/cpu-sample.c` and `tools/summarize-cpu-samples.py` provide 4ms
CPU-PC sampling and optional 32-caller local signal-frame unwinding; neither
requires perf_event access. A known burn/main control checks exclusive/caller
symbolization. Four unit tests cover PIE segment gaps, caller return boundaries,
phase filtering, truncation and rejection of unsupported ELF header bases.

Native control, PC-sampled and caller-sampled runs are sequential on CPU 2 with
one Lean thread and the same UI source/seed. Wall times are 46.062 / 45.257 /
45.802 seconds; CPU 46.020 / 45.226 / 45.771; selected CPU steal 0.51 / 0.40 /
0.36 seconds; peak sampled process RSS 3.904 / 3.909 / 3.907 GB. Throttling is
zero. These are diagnostic controls, not an optimization comparison. The
unsampled native boundary times are decode 26.815, lowering 4.650, preparation
10.486, bootstrap 1.386 and post-bootstrap interpretation 0.838 seconds.

The PC run collects 11,200 samples; the caller run has 1,127 lowering samples,
1,507 runtime-value-validation samples and 713 backtrace-preparation samples.
The principal remaining costs are:

- Exporter structural sharing: 9.501 seconds in an unsampled 28.684-second
  export/reference run. A sampled 27.595-second control attributes about 49% of
  sharing stacks to recursive `WireKey::hash::walk`, and 38% to HashMap
  `reserve_rehash` (overlapping paths). Keys are structurally rehashed on table
  growth and get/insert operations. Caching the exact structural digest and
  avoiding duplicate hashing are the next local candidates; full key equality
  must remain authoritative on collisions.
- Exporter obligation/diagnostic collection: 2.478 seconds. Sampled stacks split
  approximately between `catalog_evidence_obligations::walk` and
  `retained_vtable_probe_diagnostics::walk`; about 35% include path-string
  formatting. Lazy path rendering/relative-path summaries may reduce work while
  retaining every ordered obligation and diagnostic occurrence.
- Runtime JSON value validation: about six seconds. It repeats contextual graph
  traversal and creates/disposes temporary summaries and memo entries. PC and
  caller samples both show substantial reference-counting work (roughly a
  quarter to a third of this interval), alongside node traversal/hash maps.
  It remains necessary validation, not guest instruction execution.
- MIR lowering: 4.650 seconds. About 58% of sampled lowering stacks include
  `sourceBodyMatches`, 38% include its `typedValueMatchesSource`, and 33% include
  `payloadObligations`. These are overlapping cumulative observations, not
  additive timings. Source consistency calls `decodeCompilerValue` again for
  already decoded statements/terminators and then compares typed values. A
  checked source-bound cache/certificate could reuse outcomes without accepting
  caller-modified MIR or dropping the original obligations.
- Backtrace/source-map preparation: about 2.9 seconds. About 89% of exclusive
  samples are array copy/free paths. Caller stacks lead through
  `CompilerBacktraceSource.spans` → `lowerCompilerSpanWithInterner` → span
  interning and its HashMap insertion. Copy-on-write candidate-table arrays,
  rather than source-map queries themselves, dominate. The interner retains
  the previous candidates as a fallback; making index updates exclusive while
  preserving exact span identity/error behavior is a localized next target.
- Source JSON reflexivity: about 1.6 seconds of full structural comparison.
  This is a real checked prerequisite for existing pointer shortcuts; it cannot
  simply be assumed away.

Thus the next small changes should address cached structural hashes/rehashing
and span-index ownership, then duplicate decoding/validation. JSON parsing alone
is about two seconds. Large gains may still require a checked prepared data
representation, but no evidence here requires immediately replacing the whole
interpreter or skipping checks. Realized savings and the half-time goal remain
unmeasured by this diagnostic-only change.

All three native runs retain exactly the prior complete choice tape, events and
exit-zero terminal observation. Both fresh exporter snapshots have independent
pinned Miri references and verified FNV/length bindings. Artifact/input hashes
are unchanged; counters and traces are under ignored `scratch/perf-unops-remaining/`.
Quick/source-integrity checks pass with 92 Python tests. No full UI sweep or
Lean proof/axiom audit was rerun because interpreter/proof sources are unchanged.
Caller samples are truncated and cumulative percentages overlap; generic helper
names can be aliases after identical-code folding. The observations identify
candidates, not measured speedups or a guarantee for other guests.

### Public Rust-source-to-result accounting

The user clarified the performance boundary as Rust input → lean-miri result,
not a frozen executable phase or a UI-harness run. Earlier approximately
72-second figures sum prebuilt export/native phases; they omit the public entry
build checks and are not a measured complete user invocation. Their UI seed,
compiler flags and reference-generation settings also differ from normal use.

The original unops Rust file was measured through the actual public commands:
`build-exporter.sh` (ordinary features), `export-mir.sh --root main` with the
prepared AllocId world, and `run.sh` with no seed/UI/profile override or Miri
reference generation. Pinned toolchains and MIR sysroot were already installed;
their installation/download time is excluded. The first observation required
rebuilding the generic Lean runner (1122 Lake jobs); the second repeats exactly
the same commands with valid build caches. These are environment observations,
not a paired optimization benchmark: affinity is inherited (not fixed to CPU 2),
Lean threads are one, and there is no implementation change.

| Public source-entry stage | Rebuild needed, seconds | Build cache valid, seconds |
| --- | ---: | ---: |
| Exporter build/check | 11.864 | 0.041 |
| Rust → exported MIR | 27.770 | 30.042 |
| Runner build/check/load before first native marker | 296.658 | 0.804 |
| Read/strict decode | 26.082 | 26.263 |
| MIR lowering | 4.414 | 4.583 |
| Provider/runtime preparation | 10.294 | 10.288 |
| Remaining startup, execution, final result and teardown | 3.718 | 3.735 |
| Complete entry through process exit | 380.803 | 75.760 |

The first human-readable finalized-exit observation arrives at 379.119 /
74.046 seconds from entry; the structured result arrives at 380.796 / 75.753.
Totals include the final-result/output tail rather than stopping at guest exit.
Cumulative child CPU is 423.471 / 75.697 seconds (the build may use parallel
workers despite one Lean thread); peak process-group RSS 4.954 / 4.928 GB.
Selected-CPU-2 steal is 1.70 / 0.01 seconds, not a correction for all inherited
CPUs; cgroup throttling is 0.004645 / 0 seconds.

Both invocations pass strict readiness and finalize exit zero, with exactly
matching complete default-mode choice tapes/events (1361 choices). The rebuilt
runner's SHA256 equals frozen `7fb2fa62`, confirming that previously compiled
entry results remain semantically relevant while their build time was omitted.
Sources are unchanged; raw commands, boundaries, build logs, hashes and resource
counters are under ignored `scratch/perf-whole/`. An earlier aborted profiling
wrapper attempt is separate and is not included in either successful total.

The whole-source target must now be evaluated at this public boundary, reporting
cache state. Rebuild-needed latency is dominated by compiling the library runner;
cache-valid latency is dominated by exporting MIR (~30 seconds) and reading,
lowering and preparing it (~41 seconds). A Rust-program-specific Lean build is
not required by this JSON/native path. The existing cache already reuses the
generic runner; blindly bypassing a stale build would risk running old semantics.
No new speedup is claimed, and the half-time goal remains open for the complete
source-to-result path. Runtime, exporter and proof sources were not modified by
this scope correction; no full UI sweep or proof/axiom audit was rerun.

### Indexed execution images and checked MIR reuse

The default exporter now interns immutable construction payloads while building
and emits `lean-miri-prepared-image` version 1: a field-name dictionary and
bottom-up typed rows with dense transport IDs. The output table remains typed
Rust data through direct serialization, rather than constructing another large
JSON Value tree. IDs do not replace Rust allocation/type/instance identity.
`LEAN_MIRI_PREPARED_IMAGE=0` retains shared-payload schema 2 output; both are
accepted by Lean and the maintained Python readers. The independent
`legacy-json` builder/encoder feature is retained.

The Lean loader checks every row, edge, field dictionary and object order,
including unused rows, while constructing its indexed traversal and local
hashes/interest summaries. A resolver-produced capability restricts the private
typed MIR memo to canonical indexed roots. Checked typed decodes are reused by
node ID plus complete decoding context; source consistency checks still bind
results to the full canonical raw value and source path. Errors fall through to
the original occurrence decoder. No readiness/UB check, compiler evidence,
source program, nondeterministic policy or runner limit was removed. Default
execution still reports `iteration_limit=none`.

On the unchanged upstream `unops.rs`, three sequential alternating pairs compare
pre-change executables from `0d7e4fa9` with implementation `cb4a1dea`. The continuous
source-entry clock includes the same cache-valid exporter and runner build checks,
fresh Rust export, native decoding/lowering/preparation, execution, output and
process teardown. The old/current executables are frozen separately; the common
build gates validate the current cached build, then each trial intentionally runs
its selected executable. These are whole-source trials, not sums of separately
measured phases or a cold-build comparison. CPU affinity is 2, Lean threads one,
ordinary exporter features, prepared AllocId world enabled, `--root main`,
`--crate-name unops --edition=2021`, no UI/seed/profile override and no independent
Miri reference in the timed path. Pinned toolchains and MIR sysroot are installed.

| Metric (independent medians) | Before | Indexed image |
| --- | ---: | ---: |
| Complete source entry through native exit, seconds | 75.147 | 57.724 |
| Fresh Rust export, seconds | 28.286 | 17.632 |
| Complete native process, seconds | 46.368 | 39.897 |
| Read/strict decode, seconds | 26.943 | 23.521 |
| MIR lowering, seconds | 4.625 | 2.420 |
| Provider/runtime preparation, seconds | 10.839 | 10.636 |
| Cumulative child CPU, seconds | 74.614 | 57.291 |
| Sampled peak process-group RSS, decimal GB | 4.928 | 2.784 |
| Export bytes | 277,818,584 | 116,090,756 |

Whole-source latency is 23.2% shorter, output 58.2% smaller and sampled peak RSS
43.5% lower. Phase medians are independent and need not sum to the whole median.
The three whole-source observations are 75.147 / 75.006 / 75.582 seconds versus
57.647 / 57.724 / 58.319. CPU-2 steal deltas are 0.47 / 0.63 / 0.53 versus
0.44 / 0.49 / 0.33 seconds; cgroup throttling is zero in every trial. The final
wall boundary excludes post-exit manifest hashing; the raw collector's slightly
larger wrapper wall is also retained. Fresh export hashes are recorded per trial;
byte identity of separately generated MIR documents is not assumed. All six
complete native outputs, including all 1361 choices and their events, are
byte-for-byte identical and finish with strict readiness and exit zero.

A separate actual public invocation of `build-exporter.sh`, `export-mir.sh` and
`run.sh`, with the same ordinary settings and CPU affinity, takes **59.729 seconds**
through process exit (export 18.792, run.sh including its cached Lake gate 40.898).
It also passes readiness and produces the identical complete native output.
This is one current-version observation, not an additional paired speedup claim.
No new rebuild-needed timing is claimed: changing the library required a generic
1122-job native rebuild during development, kept outside these warm trials.

The prior 45–50-second estimate was optimistic and the whole-source half-time
goal remains open. The remaining measured costs are approximately 23.5 seconds
of decoding/checking and 10.6 seconds of preparation. A separate frozen native
profile finds JSON text parsing only 1.01 seconds and graph loading 1.36 seconds;
changing JSON syntax alone cannot recover the remaining gap. Larger spans include
runtime-value validation (6.21 seconds), document construction (5.04 seconds,
partly nested with document substeps), allocation-world validation (1.77 seconds),
backtrace-source preparation (3.06 seconds) and source equality (1.29 seconds).
Further substantial work needs typed compiler-metadata tables and reusable checked
preparation results; the present generic compiler-metadata interpretation still
runs. These profiling spans overlap and are not additive whole-path timings.

Validation on this implementation: normal exporter 21 unit tests plus 9 integration
tests; legacy-json 10 plus 9; Python suite 92 tests plus 4 dedicated reader checks;
legacy ID/first-error/shared-reference checks and indexed/legacy parity on 16
retained genuine/malformed-ID cases; final cached/uncached image checks on 2 cases;
all 13 rvalue/12 statement/15 terminator lowering branches and typed-mutation
checks; 328 compiler ABI memo candidates and collision/source fallback checks;
axiom audit of 71,209 declarations (only propext, Quot.sound, Classical.choice).
Fresh final-artifact upstream UI comparisons pass `pass/unops.rs` and
`fail/uninit/uninit_byte_read.rs`, including same-TyCtxt snapshot fingerprints
and the expected UB category/location. This is finite comparison evidence; a full
UI sweep and a general decoder/whole-machine equivalence proof were not performed.

Raw commands, counters, per-trial hashes and complete logs are under ignored
`scratch/perf-image/`, with paired summaries in `source-pairs/summary.json`, the
actual public observation in `source-pairs/public1.json`, profiles in
`final-profile/` and final UI evidence in `ui-final/`. Frozen old exporter/native
SHA256 prefixes are `12d32278` / `7fb2fa62`; current prefixes `67014ea0` /
`0eaa49db`. An early typed-cache diagnostic was interrupted after discovering
copy-on-write table copies; ownership was corrected before all reported trials.

### Compiler payload sharing, indexed diagnostics and persistent span preparation

Implementation `e538c05a` shares checked compiler instance kinds and complete
generic arguments between import and preparation. Source definition slots are
rebound to each consumer's current tables; current type membership is rechecked.
Memo keys include complete canonical kind/argument payloads. Failed parses and
changed inputs retain the independent raw decoder and its original first error.
Runtime argument validation consumes the same complete typed projection with
ordered diagnostic rebasing. Dense transport IDs select runtime context buckets
directly; inline/raw inputs keep the exact-key hash map. All decoding context
flags remain in the key.

Baseline CPU sampling found repeated retained-query path scans dominating the
previous roughly five-second document span. Indexed imports now look up the
exact canonical path, preserving ancestor debug-payload exclusion; unusual path
syntax, noncanonical indices and uncached imports retain the reference scan.
No diagnostic is dropped or newly classified from a name alone. Span candidate
indices now use persistent hash tries: a deferred-error branch can retain its
old state without copying/freeing the whole index at every successful update.
Complete span equality, first matching indices, conflicts and rollback remain.
The existing prepared MIR/span memo is also threaded through instance bodies and
promoted bodies; previously that parser path used its empty default memo. The
runtime-document exact-equality proof module includes every new cache field,
with the same conditional Json/pattern equality assumptions.

Three alternating, sequential whole-source pairs compare the previous indexed
implementation (`ca69a0d5`, native SHA256 `0eaa49db`) with this implementation
(native `880aeb08`). Both use the unchanged frozen ordinary exporter `67014ea0`,
the original unops Rust source and flags, CPU 2 and one Lean thread. As in the
previous source-entry experiment, both include common current cache-valid Cargo
and Lake checks, fresh export, all native stages, final output and process exit
on one continuous clock. No UI/seed/profile override or Miri reference runs in
the timed path. Installed toolchains/sysroot and generic runner rebuilds remain
outside these warm observations. Per-trial export hashes are retained; fresh
export byte identity is not assumed.

| Metric (independent medians), seconds | Previous indexed baseline | Compiler metadata reuse |
| --- | ---: | ---: |
| Complete source entry through native exit | 59.193 | 48.033 |
| Rust export | 18.047 | 18.032 |
| Native process | 40.516 | 29.559 |
| Read/strict decode | 23.778 | 17.119 |
| MIR lowering | 2.475 | 2.224 |
| Provider/runtime preparation | 10.680 | 6.974 |
| Cumulative child CPU | 58.714 | 47.629 |

The complete path is **18.9% shorter**; native execution including
loading and preparation is 27.0% shorter. Independent phase medians do not
add to the whole. Whole times are 59.193 / 59.269 / 58.453 seconds versus
48.033 / 48.402 / 47.783; CPU-2 steal deltas 0.52 / 0.64 / 0.37 versus
0.58 / 0.63 / 0.29, with zero cgroup throttling. Rust exporter sources and output
format are unchanged. All six complete native outputs and 1361-choice tapes/events
are byte-identical, pass strict readiness and finalize exit zero. A separate actual
public build-exporter/export-mir/run.sh invocation takes **48.433 seconds**
through exit and has the same complete output. Post-exit manifest hashing is
excluded from those end boundaries; raw collector wrapper times are also retained.
No cold-build or small memory-change speedup is claimed.

The final profile and complete phase measurements are retained under
`profile-final/` and `source-pairs-final/`. The estimated 40–45-second whole-source
time and the half-time goal remain unmet. The source table covers instance kinds
and arguments, not every compiler-metadata family; other metadata/reference
processing, source equality and allocation-world checking still run. The final
profile reports instance-body parsing 440ms, runtime-value checking 4.01 seconds
and backtrace-source preparation 376ms. Nested profiler spans are not additive
whole-path timings.

Validation: complete decoder check script passes, including existing ID/shared
reference checks, 16 indexed/legacy cases and 10 new retained-query/compiler
argument cases checked against both reference import and full typed projection.
The 10 cases include debug ancestors, supported/failed source status, missing or
noncanonical indices, unsupported argument tags and hard parser failures. The
instance test checks 1636 authentic rows (all hit the memo), 24 kind/error cases,
changed type contexts and changed source arguments against the independent raw
decoder, including resulting table IDs. Ordered-scan constant/lifecycle
comparison passes on 123 bodies and 191 constants; backtrace conflict/rollback
checks pass. The proof modules were freshly rebuilt (704 Lake jobs), connected
proof harnesses typecheck, and axiom audit passes for 71,350 declarations with
only propext, Quot.sound and Classical.choice. Fresh final-artifact Miri UI
comparisons pass unops and uninitialized-byte-read, including exact expected UB
category/location and same-TyCtxt snapshot bindings. This is finite comparison
evidence, not a general decoder/compiler/machine equivalence proof. A full UI
sweep and the complete standalone runtime registry were not rerun for this step;
Rust exporter sources are unchanged.

Commands, resource counters, full logs and hashes are under ignored
`scratch/perf-metadata/`: `source-pairs-final/summary.json`, `source-pairs-final/public1.json`,
`profile-final/`, `ui-final/`, `final-decoder.log`, `final-interner.log`,
`final-backtrace.log` and `final-proofs.log`. Baseline CPU attribution is under `attribution/`
and `cpu-summary.json`; sampling was diagnostic and excluded from the pairs.
An initial proof build exposed missing decidable-equality instances for the new
cache data; explicit instances were added without weakening the original
statement or assumptions, then the entire proof build/audit was rerun.

The earlier partial metadata experiment (before threading the MIR/span memo into
instance parsing) measured 58.411 → 49.763 seconds. Its original artifacts/logs
remain in `source-pairs/`, `profile/` and `ui/`; the final figures above supersede
that observation. All targeted checks, proof builds and fresh Miri comparisons
were repeated after the parser fix.

## Compiler-record experiment: not adopted (2026-11-04)

The next proposed change combined exporter-side positional records with Lean
load-time checked projections, without a cross-program or persistent cache.
Prototype `01281fa1` is retained on the local branch
`perf/compiler-record-prototype`; it is **not part of this PR's execution path**.
It covers type/allocation references, definition IDs, source positions, diagnostic
payloads, spans and source info (219,462 records in unchanged `unops.rs`). Rust
constructs these records without field-name maps. A version-2 image loader checks
the rows, prepares successful context-independent typed values, and shares checked
span results with import. Resolver-produced capabilities protect the exact-key
memo from arbitrary malformed Raw JSON; semantic parse failures retain the old
occurrence decoder and diagnostic order. Existing image version 1 and shared
payload version 2 remain accepted by the prototype.

The experiment was stopped after whole-source measurements showed too little
benefit to adopt the new format and import machinery. Three alternating sequential
pairs compare the previous metadata head `bcc9d6d0` (native `880aeb08`, exporter
`67014ea0`) with the prototype (native `84efa464`, exporter `3b5e2348`). The same
original Rust source/flags, prepared AllocId profile, installed pinned toolchains,
CPU 2, one Lean thread, ordinary exporter features and cache-valid build gates are
used. Fresh export, native result output and process teardown are inside one
continuous entry clock; independent Miri, profiling and other tests/builds are
outside the timed path.

| Metric (independent medians) | Previous implementation | Prototype |
| --- | ---: | ---: |
| Complete source entry through native exit, seconds | 47.968 | 47.327 |
| Fresh Rust export, seconds | 17.950 | 17.415 |
| Complete native process, seconds | 29.632 | 29.294 |
| Read/strict decode, seconds | 17.074 | 16.862 |
| MIR lowering, seconds | 2.238 | 2.262 |
| Provider/runtime preparation, seconds | 7.053 | 7.061 |
| Child CPU, seconds | 47.536 | 46.895 |
| Sampled peak process-group RSS, decimal GB | 2.697 | 2.774 |
| Export bytes | 116,090,756 | 113,675,080 |

Whole observations are 47.968 / 48.949 / 47.708 versus
47.258 / 47.472 / 47.327 seconds. The median difference is only 0.641 seconds
(1.34%); this small shared-host result is not evidence of a substantial speedup.
Preparation does not improve and sampled peak memory increases about 2.8%.
CPU-2 steal deltas are 0.27 / 0.43 / 0.24 versus 0.24 / 0.43 / 0.40 seconds;
cgroup throttling is zero in all six runs. All complete native outputs, including
1361 choices/events, are byte-identical and finalize exit zero with strict
readiness. A separate actual public build-exporter/export-mir/run.sh invocation
of the prototype takes 48.195 seconds with identical output. Phase medians are
independent and must not be summed.

The diagnostic prototype profile reports graph loading 1.94 seconds (previous
profile 1.44), shared decode memo 501ms (718ms), runtime-value validation 3.55
seconds (4.01), allocation-world validation 1.85 seconds, and preparation source
equality 1.34 seconds. Much of the decoding cost moved into graph loading rather
than disappearing. These nested spans overlap. The prototype still reconstructs
ordinary JSON and retains generic MIR/layout/ABI/compiler-query walks. The seven
foundation schemas alone do not implement the proposed complete typed execution
input. Reaching a materially lower whole-source time, especially the requested
20 seconds, remains unresolved: subsequent work must eliminate those intermediate
representations and repeated checks through checked typed data, while preserving
legacy input/public-model mutation checks and first-error priority. Merely extending
this positional envelope is not established as a solution. Fresh export alone
still takes about 18 seconds; a 20-second total also needs a substantial producer
improvement, not just reduced Lean preparation.

Prototype validation passed: exporter 25 unit and 9 integration tests; unchanged
legacy-json configuration 10 plus 9; Python suite 92 and dedicated reader 5;
complete decoder script including 16 version-1 and 16 version-2 indexed cases,
10 metadata/status/argument cases, 1636 authentic compiler instances and 24
kind/error cases, source/context mutations, full/runtime projections, and 11
record cases across 160 domain/tag/path contexts. Fresh Miri comparisons pass
unops and uninitialized-byte-read with expected UB category/location and snapshot
bindings. Miri/MiriTests were freshly rebuilt and connected proof harnesses
checked; axiom audit passed for 71,418 declarations with only propext, Quot.sound
and Classical.choice. These finite checks do not prove general format/compiler
or interpreter equivalence. A full UI sweep and standalone runtime registry were
not rerun. An intermediate check overlapped a rebuild and found a missing olean;
the complete decoder script was rerun successfully after rebuilding.

Only checked/proved collection bounds discovered during validation are retained
from the prototype: MIR/graph indexing uses proved bounds or explicit errors,
and an invalid prepared definition slot fails instead of producing a default ID.
These are not claimed as a performance improvement. The original format and
metadata pipeline are retained. The 20-second and further half-time goals remain
open. Raw trials, complete outputs, counters, artifact hashes and the prototype
patch are retained under ignored `scratch/perf-records/`, notably
`source-pairs/summary.json`, `source-pairs/public1.json`, `profile/`,
`prototype.patch`, `decoder-final.log`, `checked-final-proofs.log` and
`ui-final-capability/`.

After withdrawing the prototype, the retained bounds-only change was separately
rebuilt with Miri/MiriTests and checked by the complete original decoder script,
21 exporter unit plus 9 integration tests, quick/source/fixture checks, the
123-body/191-constant ordered-scan comparison and backtrace conflict/rollback
checks. Connected proofs and the axiom audit pass for 71,353 declarations with
only the three permitted axioms. Fresh restored-format Miri comparisons pass
unops and uninitialized-byte-read; the complete default-mode unops output matches
the earlier baseline byte-for-byte. The restored native hash is `2b8d238b` and
the original exporter hash is again `67014ea0`; no new latency claim is made for
the bounds changes. Logs are `restored-*.log` and `ui-restored-clean/` in the same
ignored evidence directory. The first restored UI attempt was classified as a
resource failure when the shared cgroup memory `max` event counter changed under
file-cache pressure (no OOM kill). It is not counted as passing; both comparisons
were rerun successfully after releasing reclaimable pages for local build/trial
files, without changing any input, assertion or guard.

## Exporter cost and query-closure investigation (2026-11-04)

The approximately 18-second fresh-export cost was measured on original
`upstream/miri-source/tests/pass/unops.rs`, `--root main`, `--crate-name unops
--edition=2021`, prepared AllocId world, ordinary exporter and pinned installed
sysroot. Profiling now separates direct-mode pin/argument work, compiler driver
before/after its export callback, graph encoding from source release, individual
vtable/diagnostic walks, writing and final image release. It also records
per-producer domain growth and per-round catalog sizes. This adds diagnostics,
not a new input format, query-selection policy, runtime limit or cross-input
cache. `tools/summarize-exporter-profile.py` preserves the parent/child span
hierarchy rather than summing overlapping spans.

Three sequential diagnostic runs use frozen exporter `b1a79f7a`, CPU 2, one Lean
thread, fresh output each time and no concurrent builds/tests. Their process
walls are 18.193 / 17.878 / 18.019 seconds, CPU times 18.190 / 17.877 / 18.017,
CPU-2 steal 0.19 / 0.11 / 0.12 and cgroup throttling zero. Peak process RSS is
approximately 2.130 decimal GB. These are profiling observations, not a paired
speedup experiment or whole Rust-to-guest timings.

| Export phase, independent medians | Seconds |
| --- | ---: |
| Pin and argument preparation | 0.012 |
| Compiler driver before exporter callback | 0.008 |
| Query/metadata generation before vtable patches | 10.404 |
| Two vtable patch traversals | 1.511 |
| Structural closure and retained diagnostic collection | 1.976 |
| Indexed graph encoding and raw source release | 2.945 |
| Compiler driver after callback, including cleanup | 0.745 |
| Snapshot writing | 0.151 |
| Final image release | 0.103 |
| Complete exporter process | 18.019 |

Small callback cleanup/startup gaps are not separate table rows; independent
medians must not be added into a purported exact process total. The diagnostic
subspans are graph encoding 2.094s and source release 0.840s; vtable-ID patch
0.753s and virtual-candidate patch 0.758s; rooted structural closure 0.015s,
catalog evidence 0.841s and retained vtable diagnostics 1.119s. These are children
of the table rows, not additional time. Within query/metadata generation, reaching
MIR/allocation probes takes 3.197s and foreign/virtual transfer work 1.622s across
all closure rounds. Function facts, instance ABI projections and covariance take
0.572 / 0.440 / 0.627 seconds respectively; they combine compiler calls, data
construction and repeated projection, and are not pure query execution times.

A separate pinned-rustc self-profile, recording only query providers and cache
hit counts, reports **0.296 seconds summed exclusive provider execution**. This
excludes cache-hit lookup, query framework overhead and non-query compiler APIs;
it is not an exact measure of every compiler-related operation. Representative
self times are normalization 0.040s, instance ABI 0.038s and layout 0.028s, with
223,514 / 227,203 / 588,654 cache hits. A diagnostic 4ms CPU sampler independently
finds rustc_query_impl/system frames in 78/4574 stacks (1.7%); inlining and its
32-frame depth limit make that attribution incomplete. Construction interning,
formatting, graph traversal, allocation and destruction dominate the visible
stacks. Cumulative stack percentages overlap and must not be summed.

The closure reaches a fixed point after seven rounds: 9,937 instance identities,
3,942 processed instance requests and 26,469 type IDs. Of the final instance rows,
3,628 contain MIR bodies; intrinsic/foreign/virtual dispatch rows need no body.
Early logs labeled the processed registry `emitted_mir`; the reader normalizes
that field to `processed_instances`. Per-producer growth identifies
runtime type queries as adding **17,693 type IDs and 5,902 instance identities**;
MIR/allocation probing adds a further 6,062 types and 117,778 registered allocation
ID keys. These are growth observations, not a proof that those identities are
unused or removable. Generated pointer/reference outputs are already suppressed
as fresh runtime-type demands; simply iterating only the existing demand set is
not a new optimization.

Repeated projection is also visible: 19,224 function rows, 25,149 instance ABI
rows and 48,830 helper-signature candidate rows are reconstructed across the
seven rounds, although only 3,495 / 4,427 / 8,964 rows survive in those final
catalogs. Final explicit instance ABI requests number 3,262; fallback rows cannot
be declared unused merely by subtracting this from the catalog size. The pinned
`helpers.rs::call_function` constructs the caller signature from actual argument
types, destination (including unit when absent), caller ABI and caller-location
requirement. The exporter conservatively enumerates combinations of these facts.
One successful guest trace does not justify removing variants needed by another
permitted execution. No query or catalog row was removed in this investigation.

The clearest next mechanical target is approximately **3.47 seconds of vtable
patching plus retained-diagnostic traversal**: skip immutable subgraphs that cannot
contain the relevant fields, preserving every diagnostic occurrence/path and
patch result. Encoding/source ownership is another approximately 2.95-second
area. Exact per-compilation reuse of unchanged catalog projections could reduce
rebuilding across seven rounds without introducing a cross-program cache.
Narrower per-operation type/drop-glue demands need further source/consumer
analysis before claiming that the 17,693 generated types can be reduced. Query
provider execution alone is too small to deliver a large speedup. The 20-second
whole-source goal remains unresolved; these observed costs are targets, not
promised savings.

Raw evidence is ignored under `scratch/perf-exporter-closure/`: `summary.json`,
`detailed{1,2,3}-stats.json`, `detailed{1,2,3}-phases.json`, `coarse-phases.json`,
`growth-summary.json`, `query-profile/`, `sampled-cpu.json` and
`sample-details.json`. Self-profile tooling uses measureme tag 12.0.3,
commit `5ac839c602b59eee9c908b3b35b6d6c0cd1c42f7`; its separate diagnostic build
needed warning-lint compatibility flags for two obsolete `unsafe` wrappers.
No project compiler, test expectation or semantic check was weakened.

Validation on the final recorder: normal exporter 21 unit plus 9 integration
tests, legacy-json 10 plus 9, quick/source/fixture checks and Python 96 tests
(including four profile-attribution parser cases) pass. A profiled ordinary export
runs through the unchanged native interpreter with complete output byte-identical
to the earlier default-mode unops baseline, including 1361 choices/events and
strict readiness. Fresh final-reference-exporter comparisons with profiling
enabled pass unops and uninitialized-byte-read, including snapshot binding and
expected UB category/location. The final ordinary/reference exporter hashes are
`ba3e58f2` / `60ca206e`. Lean sources were not changed, so no new Lean build/proof
audit or full upstream UI sweep is claimed for this diagnostics-only update.
Logs are `checked-rust-tests.log`, `final-legacy-tests.log`, `final-quick.log`,
`native-validation.log` and `ui-last/` in the same ignored evidence directory.
This investigation itself did not change generation ranges. The subsequent
operation-directed change is measured and validated separately below.

## Operation-directed runtime type queries (2026-11-04)

The exporter now collects separate mutable-pointer, mutable-reference and drop
requirements from all exported MIR (including cleanup blocks), Box pointees,
concrete vtables and implicit startup/backtrace/panic operations. Requirements
are not inferred from a successful guest trace. The compilation-local fixed
point includes operation-mask growth, and later operations merge into one row
per exact source type. The pinned compiler still constructs the exact types and
resolves drop glue. Null vtable drop slots retain concrete reference/drop facts
and promotion of their executable empty-drop shim.

The explicit `source_operations_v1` type-query marker permits omitted
operations; requesting an omitted operation fails. Present malformed constructor
evidence is still rejected during preparation. Unmarked legacy rows still
require both constructors. The former full-query producer remains available
with `--features full-type-queries`; its selected-allocator fixture output is
byte-identical to the frozen pre-change producer. See the requirement mapping in
[the exporter guide](exporter/README.md). No cross-program cache, guest rewrite,
runtime-limit change or successful replacement for missing semantics was added.

An ordinary diagnostic unops export reduces type IDs from 26,469 to 9,002,
instance identities from 9,937 to 4,279 and runtime type rows from 9,002 to 323.
Most remaining metadata belongs to other MIR/ABI/helper catalogs, so these
counts do not imply a proportional reduction in total input size or time.

Three alternating sequential source-entry pairs use original
`upstream/miri-source/tests/pass/unops.rs`, root `main`, crate `unops`, edition
2021, CPU 2, one Lean thread, immutable ordinary exporter/native artifacts and
the prepared AllocId world. Each includes identical current cache-valid
Cargo/Lake gates, a fresh export, all native result output and process teardown;
post-exit diagnostic manifest hashing is excluded. No UI/seed/profile override
or reference-Miri run is in the timed path. Installed toolchain/sysroot and
valid build caches are prerequisites; cold builds are not measured.

| Independent medians | Frozen pre-change | Operation-directed |
| --- | ---: | ---: |
| Rust source entry → native exit | 48.128 s | 44.540 s |
| Export | 18.120 s | 17.206 s |
| Native process | 29.373 s | 26.696 s |
| Read/strict decode | 16.967 s | 15.101 s |
| MIR lowering | 2.260 s | 1.771 s |
| Provider/runtime preparation | 7.003 s | 6.915 s |
| Sampled peak process-group RSS | 2.692 GB | 2.417 GB |
| Input bytes | 116,090,756 | 100,249,298 |

Whole observations are 48.128 / 47.999 / 48.171 versus
44.690 / 44.540 / 44.209 seconds: **7.46% shorter**, not a half-time result.
Phase medians are independent and must not be added. Child CPU medians are
47.672 versus 44.107 seconds, steal observations span 0.26–0.38 seconds and
cgroup throttling is zero. Baseline ordinary/native SHA256 prefixes are
`ba3e58f2` / `2b8d238b`; candidate `8c423774` / `8e3673f8`.
Strict readiness, finalized exit zero and all 1361 choice events/tapes agree in
all six executions. Complete outputs differ only in the existing
`canonical_body_1814` source-ID diagnostic: removing unreached compiler entries
renumbers type/instance/body IDs. Excluding exactly that line, the output SHA256
is `4d64d9a2b8f0e917eed65032df627d8aeb0b1096c7627fcb06ceec1a14542ea1`.
A separate invocation through public `build-exporter.sh` / `export-mir.sh` /
`run.sh` takes 44.453 seconds through native exit, with complete output
byte-identical to the candidate trials.

The preparation phase is essentially unchanged. This reduces unnecessary
construction/transport but does not remove the remaining generic MIR/ABI/helper
preparation walks. The 20-second and further half-time goals remain unresolved;
type-row counts alone did not predict the whole-source improvement.

Validation passes normal exporter 22 unit plus 10 integration tests, full-query
reference 22 plus 10, legacy-json 11 plus 10, and final focused producer reruns
after making its operation fixture a library (the producer check needs no std
main wrapper). A fresh binary fixture separately asserts two observable drop
calls and exercises borrowed-only types, Box, virtual calls and null-slot dyn
drop; both same-prepared-TyCtxt Miri and Lean exit zero. Full decoder checks pass,
including 16 indexed cases, 10 metadata cases, 1636 authentic instance rows,
24 kind/error cases and new sparse/legacy/malformed operation checks. Quick,
source/fixture checks and Python 96 pass. The native/MiriTests build, 47 runtime
checks, connected proof harnesses and transitive axiom audit for 71,356
declarations pass (only propext, Quot.sound and Classical.choice).

Fresh final-reference/native upstream comparisons pass unops,
uninitialized-byte-read (including expected UB category/site), packed dyn traits,
panic catch/unwind and ZST Box. The first multi-check attempt classified panic
and ZST Box as resource failures when shared cgroup memory events changed under
file-cache pressure, without an OOM kill. Those attempts are not counted as
passes; both were rerun successfully with stable event counters after releasing
reclaimable workspace file pages. An intermediate legacy fixture shell failed
after its script was edited while running; clean final reruns pass. No guard or
expectation was weakened. No complete upstream UI sweep or general exporter /
machine-equivalence proof was performed.

Evidence is ignored under `scratch/perf-demand-types/`: `source-pairs/summary.json`,
per-trial manifests and logs, `unops-export.log`, `ui-focused/`,
`ui-resource-rerun/`, `operations-counter*`, `decoder.log`, `rust-tests-final.log`,
`full-tests.log`, `legacy-tests-final.log`, final focused fixture logs,
`quick-final.log`, `connected.log` and `runtime-tests.log`. Frozen binaries and
source-entry collection/analysis scripts are retained there for reproduction.

## Complete producer-side execution-IR experiment (2026-11-05)

A whole-pipeline prototype moves **all** checked decoding, MIR lowering,
compiler/provider preparation and initial allocation registration into the
exporter, then passes one opaque typed execution IR to the unchanged interpreter
in the same Lean runtime. It covers types, MIR, allocations, ABI, scopes,
constants, virtual/drop calls, frames, startup and remaining provider registries;
it is not an ABI-only experiment. No input-specific shared cache is used.

The implementation reuses the existing compiled Lean checks inside the exporter.
It is **not** a Rust-native rewrite of semantic metadata emission, nor does it
erase all internal JSON evidence or runtime query decoding. Typed native source
rows avoid JSON text/file transfer, row-envelope reconstruction and decimal
reparsing for unsigned integer leaves. Every row/edge/dictionary entry (including
unused rows), source pin, semantic obligation, strict-readiness condition and
preparation error is still checked. The native traversal capability has a private
witness of a successful checked resolver; no producer readiness bit or unchecked
serialized Lean heap is accepted. Existing serialized input contracts remain
unchanged on the prototype's ordinary entry.

The C bridge uses pinned Lean constructors, owned reference transfers and an
opaque same-runtime IR. Interpretation uses the same `lean_run_main` runtime
thread/stack policy as the standalone runner. A transient in-call ownership
handoff is cleared before interpretation; it retains no cross-program data.
Same-TyCtxt Miri comparisons bind the exact captured snapshot to the in-memory
image and independently check its terminal/UB category/site. Reference UB keeps
its original nonzero process status and cannot pass without a matching Lean
terminal. The shared library is fixed interpreter code, not a program cache.

Three alternating sequential pairs use unchanged original unops source, root
`main`, crate `unops`, edition 2021, prepared AllocId world, CPU 2, one Lean
thread and frozen ordinary exporter/native or IR exporter/library artifacts.
Both include identical current cache-valid code-build gates, fresh compilation,
all producer-side validation/preparation, guest execution, output and final
process teardown. Reference Miri, UI/seed/profile overrides and program-data
caches are absent from timings. Installed toolchains/sysroot and valid code
build caches are prerequisites; cold builds are not measured.

| Independent medians | Retained two-process entry | Complete producer-side IR |
| --- | ---: | ---: |
| Rust source entry → final process exit | 42.940 s | 40.179 s |
| Entry → semantic reader boundary | 17.195 s | 17.580 s |
| Graph/semantic read and checks | 14.586 s | 11.769 s |
| MIR lowering | 1.706 s | 1.745 s |
| Provider/runtime preparation | 6.696 s | 6.357 s |
| Sampled peak process-group RSS | 2.414 GB | 3.501 GB |
| Child CPU | 42.502 s | 39.769 s |

Whole observations are 43.797 / 42.924 / 42.940 versus
40.145 / 40.179 / 41.487 seconds: **6.43% shorter**, with approximately **45% more
peak RSS**. Independent phase medians must not be added. All six complete
outputs are byte-identical, including strict readiness, finalized exit zero and
1361 choices/events. Output SHA256 is
`47a681990447e340c09c71f7a503a9cc8d034ab5019506f3a6826c072a66de67`.
Steal observations span 0.29–0.49 seconds and cgroup throttling is zero. A separate
invocation through the public `execute-rust.sh` command takes 40.360 seconds with
identical complete output. The baseline differs from older 44.5-second records
because these are new paired measurements; earlier and current samples must not
be mixed into one speedup claim.

Measured baseline exporter/native SHA256 prefixes are `8c423774` / `8e3673f8`;
IR exporter/library prefixes are `94236b6e` / `5156be41`. Compilation still builds
the source metadata and runs the existing semantic preparation. Merely moving
those functions into the producer does not eliminate their cost. This experiment
does not meet the further half-time or 20-second goal, and does not establish an
upper bound for a future direct semantic typed-emission design. It is not
recommended as the default entry given the small whole-source gain, increased
memory and native embedding surface. Preserve the prototype for review; retain
the existing default execution pipeline.

Validation of the prototype passes exporter `execution-ir` 22 unit + 10
integration tests, legacy-json 11 + 10, Python 96, quick/source/fixture checks,
the complete decoder script, and native typed-image parity tests for unused-row
errors, dictionaries, source graphs/digests, readiness and canonical lowered MIR.
Native/MiriTests builds, 47 runtime checks, connected proof harnesses and the
71,433-declaration axiom audit pass (only propext, Quot.sound and Classical.choice).
Finite IR comparisons pass unops, ZST Box, packed dyn traits, uninitialized-byte
UB and panic catch/unwind. After the final embedding fix, a fresh final-library
run passes panic, unops and uninitialized-byte-read with stable source identities
and memory-event counters. No full UI sweep or general translation/equivalence
proof was performed.

Intermediate failures are not counted as passes: mixed C/Rust stream buffering
split a long UB terminal JSON line (fixed by flushing before returning to Rust);
the initial embedded run overflowed Rust's smaller stack while printing 102560
choice events after guest exit (fixed by Lean's normal main-thread entry).
That earlier panic attempt also observed source edits during comparison and was
invalidated by the unchanged source guard. No oracle, resource guard or expected
outcome was weakened. Subsequent successful reruns use immutable artifacts.

Raw evidence and immutable binaries are ignored under `scratch/perf-execution-ir/`:
`source-pairs/summary.json`, per-trial manifests/logs, `public-entry.log`,
`ui-focused/`, `ui-negative-rerun/`, `ui-final/`, `ui-stack/`, `decoder.log`,
`image-checks.log`, `rust-tests-final.log`, `legacy-tests.log`, `quick-final.log`,
`connected.log` and `runtime-tests.log`. The collection and analysis scripts are
retained there. The prototype source is preserved at `2b08ad39` on `perf/full-execution-ir`
and in [draft PR #17](https://github.com/proofs-rs/lean-miri/pull/17);
the retained PR #9 only records its outcome.

## Compiler allocation-catalog normalization (2026-11-05)

The retained two-process path now removes repeated compiler allocation metadata
rather than moving the same semantic preparation into another process. The
exporter keeps all caller-location span coverage, but captures one exact compiler
Location template per filename and each span's effective u32 coordinates. The
interpreter constructs a fresh immutable root for every intrinsic invocation,
using compiler field offsets and the existing checked scalar writes. Filename
CTFE provenance, untouched bytes, initialization and per-call identity remain
separate. The pinned `const_caller_location` is an uncached hook; these templates
must never turn repeated guest calls into a single shared root. The
`full-caller-locations` feature retains the literal reference producer.

Prepared allocator worlds use `rustc_alloc_id_world_v2`: a dense ASCII source-kind
column and sparse opaque-memory projections replace the repeated raw-pool JSON
objects. Supported-node facts come from the existing allocation table. Lean
reconstructs the full typed pool and retains the complete prefix/frontier,
source/graph bindings, salt/key checks and exhaustive byte-family validation.
Unknown mutability, noncanonical byte keys, mixed encodings and missing or
repeated opaque projections fail. Legacy v1 parsing and the exact raw/typed
binding validator remain available; `full-allocation-world` emits v1 reference
facts. No program cache, trace pruning, guest rewrite, iteration limit or
readiness/UB/provenance bypass was introduced.

Three final alternating sequential pairs use unchanged original unops source,
root main, crate unops, edition 2021, CPU 2, one Lean thread, frozen binaries and
fresh exports with the prepared AllocId world. Both paths include current
cache-valid Cargo/Lake gates, complete output and final child exit; post-exit
input hashing is excluded. Installed toolchains/sysroot and build caches are
prerequisites, not cold-build measurements. The chronological retained order is
baseline3/candidate3, candidate2/baseline2, baseline1/candidate1. Earlier collector
observations that included diagnostic hashing are retained separately and are
not used below.

| Independent medians | Retained baseline | Normalized catalogs |
| --- | ---: | ---: |
| Complete Rust source entry → process exit | 43.420 s | 36.020 s |
| Export | 16.751 s | 14.733 s |
| Read/strict decode | 14.666 s | 10.810 s |
| MIR lowering | 1.772 s | 1.691 s |
| Provider/runtime preparation | 6.764 s | 5.664 s |
| Child CPU | 42.963 s | 35.588 s |
| Sampled peak process-group RSS | 2.407 GB | 2.112 GB |
| Input bytes | 100,249,298 | 70,498,621 |

Whole observations are 43.878 / 43.074 / 43.420 versus
35.245 / 36.034 / 36.020 seconds: **17.04% shorter**. Phase medians must not be
added. Steal spans 0.14–0.41 seconds and throttling is zero. A separate public
build-exporter/export-mir/run.sh invocation takes 35.895 seconds. Every complete
output is byte-identical, including strict readiness, exit zero and all 1361
choices/events; SHA256 is
`47a681990447e340c09c71f7a503a9cc8d034ab5019506f3a6826c072a66de67`.
Frozen baseline exporter/native prefixes are `8c4237746c21` / `8e3673f8b388`;
final normalized prefixes are `c672ed3b8870` / `e8db14b4a226`.

Validation passes normal exporter 22 unit + 10 integration tests, legacy-json
11 + 10, the complete decoder script, Python 96 and quick/source/fixture checks,
47 rebuilt self-contained runtime checks, connected proof harnesses and the
71,390-declaration axiom audit (only propext, Quot.sound and Classical.choice).
`tools/check-compact-input.sh` passes genuine v1/v2 full-pool/catalog/frontier and
other-document-field equality, independent Lean world equality and malformed
input controls. It compares all 183 source spans in a macro/track-caller fixture
against actual compiler images under four location-detail settings. Immutable
construction checks cover both endiannesses, pointer/provenance retention,
uninitialized padding, source isolation, bounds and guest-write rejection.
Literal/recipe query controls also cover u32 limits and malformed evidence.

Fresh same-prepared-TyCtxt Miri comparisons pass unops, uninitialized-byte-read
with its independent expected UB category/site, panic catch/unwind, and the
separate maintained caller-location fixture (macro/track-caller coordinates and
fresh identities for repeated calls). The reusable entry for the last case is
`tools/check-caller-location-runtime.py`; it does not extend the upstream
inventory. The initial panic attempt exposed an incorrect exactly-three-fields
assumption; the pinned Location has a fourth zero-sized PhantomData field.
The adapter now follows the compiler's projection of its first three fields.
That failed attempt is not counted as a pass.

Two broader controls remain unpassed. `pass/track-caller-attribute.rs` stops with
a rustc closure-signature ICE (collect.rs:1244); the frozen pre-change exporter
reproduces it. After the field fix, `pass/panic/std-panic-locations.rs` stops at
`cast compiler query: type kind is outside the cast operand domain`; a fresh
fully materialized caller-location control reaches the same Unsupported result.
Neither is an agreement/pass, and neither expectation was weakened. No full UI
sweep or general compiler/interpreter equivalence proof was performed.

**The 20-second goal remains unmet.** Export, semantic import and preparation
still dominate this short guest. Further work must reduce repeated producer and
consumer representations together; moving the existing checked pipeline into
the exporter alone was insufficient (separate PR #17 above). Investigate shared
allocation payload templates and direct typed semantic metadata while preserving
all source identity/binding checks, legacy errors and maintainability; avoid
cross-program caches. Evidence, collection scripts and immutable artifacts are
ignored under `scratch/perf-catalog-redesign/`: `final-source-pairs/summary.json`,
per-trial manifests/logs and losslessly compressed inputs, `public-entry.log`,
`compact-entry-check.log`, `caller-producer-comparison.log`, `world-checks-final.log`,
`template-checks-final.log`, `caller-checks.log`, `decoder.log`, `rust-tests.log`,
`legacy-tests.log`, `runtime-checks-final.log`, `connected.log`, `quick-final.log`,
`ui-focused/`, `ui-location-fixed/`, `ui-location-literal/` and `caller-runtime-final/`.

## Compiler-owned construction and exact consumer reuse (2026-11-05)

The default exporter keeps its immutable construction graph on the compiler
thread with Rc/OnceCell. Only the finished typed image (or explicit legacy JSON
snapshot) crosses the worker boundary. Small objects use ordered flat fields;
static protocol field names are borrowed, and repeated scalar strings are
looked up before allocating an owned candidate. Compiler-owned ABI addresses
provide a projection cache before the existing structural ABI cache. Pointer
addresses never replace compiler identities, and all hash collisions still
require complete exact wire equality. Cached sort keys retain stable tie order.
Numeric interning retains floating-point spelling, including negative zero.

Producer diagnostic scans now memoize relative results over construction nodes,
including empty branches. Every occurrence is emitted in its original traversal
order with its original path; debug-payload suppression remains unchanged.
Independent test-only copies of the previous walkers compare duplicated/shared
branches and diagnostics. This reduces repeated graph scans and path allocation
without pruning exported facts or query demand.

The reader reuses the checked graph's JSON digest for compiler-argument bucket
selection while retaining full key equality and the original raw fallback.
Required type/instance membership uses sets without changing result order.
Unchanged allocation payload wire comparisons and source-span interning use
proved pointer shortcuts. Imported supported allocation arrays carry a private
owner binding plus a checked self-equality certificate, so the three startup
catalog checks can reuse their original comparison result. Theorems equate
both wire comparison and image-owner comparison to their historical predicates;
nonreflexive malformed JSON retains the full fallback. No interpreter, resource
limit, readiness gate, UB check or source identity policy changed.

Three alternating sequential pairs use original unops/root main/crate unops/
edition 2021, prepared AllocId world, CPU 2, one Lean thread and immutable
exporter/runner artifacts. Timings include current cache-valid code build gates,
fresh source export, checks/preparation, execution, all output and process exit;
post-exit evidence hashing is excluded. There is no shared program-data cache.

| Independent medians | Retained 4583a2ec | New construction/reuse |
| --- | ---: | ---: |
| Rust source entry to final exit | 36.632 s | 28.440 s |
| Export | 14.975 s | 7.935 s |
| Semantic decode/checks | 11.199 s | 10.629 s |
| MIR lowering | 1.740 s | 1.731 s |
| Preparation | 5.706 s | 5.860 s |
| Child CPU | 36.217 s | 28.082 s |
| Sampled peak process-group RSS | 2.115 GB | 2.114 GB |

Whole trials are 36.559/36.632/36.790 versus 28.921/28.440/28.407 seconds,
**22.36% shorter**. All six complete outputs are byte-identical (the same
47a68199… SHA256 recorded above), strict readiness is zero, finalized exit is
zero and the choice/event cursor is 1361. Steal is 0.24–0.46 seconds and cgroup
throttling is zero. Independent phase medians must not be added. Separate
compilations may reorder compiler query-only helper type IDs; input byte
identity is not claimed. Evidence and immutable artifacts are under ignored
`scratch/perf-owned-graph/`, especially `source-pairs/summary.json` and trial
manifests/logs; old large inputs are losslessly compressed.

Validation passes ordinary exporter 29 unit + 10 integration tests, legacy-json
13 + 10, the full decoder comparison script, Python 96 and quick checks,
Miri/MiriTests/native builds, 47 rebuilt runtime checks and the 71,433-declaration
axiom audit (only the three permitted axioms). New owner-binding controls compare
foreign/mutated/independently reconstructed arrays, duplicate IDs and deliberately
nonreflexive malformed JSON; span-interner sequence/error comparisons also pass.
Fresh same-TyCtxt Miri comparisons pass unops, uninitialized-byte-read UB with
its expected category/site, panic catch/unwind and the maintained caller-location
fixture. The first panic/caller attempts were invalidated by cgroup memory-event
changes during concurrent checks, not accepted as passes. After releasing unused
build/evidence file-cache pages and serializing the comparison reruns, both pass
with unchanged guards. No full UI sweep or whole-machine equivalence proof ran.

A tested transient replacement of the persistent span-candidate map with a
copy-on-write hash map made backtrace preparation much slower through repeated
copies; it is reverted. Keep the persistent index for shared incremental states.
**The sub-20-second goal is still unmet.** Reader/preparation and producer work
remain material. Next investigate direct checked graph transport/semantic rows
that avoid intermediate JSON trees, plus shared allocation payload templates.
Do not adopt the rejected embedded-Lean IR experiment or cross-program caches.

## Direct checked graph transport and runtime traversal reduction (2026-11-05)

At revision `789a56f8`, the sub-20-second Rust-source-to-final-result goal
remained **unmet**; the follow-up below supersedes that outcome. This
experiment improves the original, untouched upstream `unops.rs` entry from
28.612 to **24.850 seconds** (13.15% shorter); it does not justify claiming a
further halving. No cross-program cache, source rewrite, omitted standard
startup, default guest budget or producer readiness assertion is introduced.
The rejected complete embedded-Lean execution-IR experiment above stays rejected.

The exporter can write `--binary-image` (`LMIRIMG` version 1) directly from its
finished typed image. No generic JSON transport tree is constructed or parsed
on this path. The Lean reader constructs the existing checked runtime graph,
checking all dictionary entries, rows, backward edges, scalar encodings, root
and trailing bytes, including unused rows. JSON remains supported and is still
the exporter's default. Binary integers are canonical bounded u64 LEB128; string
UTF-8 and exact non-integer numeric spellings, including negative zero, survive.
These wire bounds do not impose an interpreter execution budget.

Both readers compute conservative runtime-parser summaries locally. A branch
can be omitted only when its summary is discarded, its decoding context is
unrestricted/untagged, and it contains no relevant checks. Enum contexts, MIR
roles, HIR retention, source span/info markers, unsupported statuses and ordered
obligations retain their original behavior. Legacy/raw inputs use a conservative
fallback. Existing four-bit producer scan flags are unchanged. MIR tag recognition
is factored into one module rather than copied into the graph reader.

Allocation parsing returns erased, private-constructor origin evidence indexed
by the exact raw document, typed allocations and allocation world. Internal
consumers reuse that first successful parse; modifying any indexed value requires
dropping the evidence and revalidating. All initial world, body/reference, dense-ID,
readiness, installation/crosswalk and runtime checks remain. The historical raw
validator and `validateAllocationWorld_eq` theorem are unchanged. The new witness
proves parse origin, not whole-machine safety or a general theorem equating the
old opaque JSON Boolean predicate with the new path. Genuine-input comparisons
exercise that independent old validator as well as foreign raw/model rejection.

The producer also reuses compiler-owned generic-argument projections within one
TyCtxt, with separate query-suppression roles. Debug assertions re-run each hit
and compare its output and type-demand/operation/registration effects. A fresh
unops export with these assertions enabled passed. Release builds use ThinLTO
and one Rust codegen unit; project native objects/linking also use ThinLTO with
four linker workers. These are build optimizations, not semantic shortcuts.

Three alternating sequential pairs, fresh exports, frozen executables, CPU 2,
one Lean thread, cached tool build gates included, end at final child exit:

| Complete entry or phase | Previous graph | This experiment |
| --- | ---: | ---: |
| Rust source to final result | 28.612 s | 24.850 s |
| Export | 7.967 s | 7.609 s |
| Decode and checks | 10.689 s | 7.891 s |
| Lower | 1.750 s | 1.715 s |
| Prepare | 5.808 s | 5.498 s |
| Run to terminal marker | 0.950 s | 0.897 s |

Phase medians must not be added. Whole trial spreads are
28.564/28.616/28.612 versus 25.331/24.570/24.850 seconds; CPU medians are
28.246 versus 24.519 seconds. Peak sampled group RSS is 2.124 versus 1.807 GB.
Same-core steal is 0.17–0.37 seconds and cgroup throttling is zero. All six full
outputs have SHA256 `47a681990447e340c09c71f7a503a9cc8d034ab5019506f3a6826c072a66de67`,
zero readiness obligations, finalized exit 0 and 1361 events. Independent fresh
compiler inputs need not have identical helper type-ID ordering. Frozen artifacts,
trial manifests, logs and phase summary are under ignored
`scratch/perf-direct-checked-graph/source-pairs/summary.json` and its parent.

Validation: ordinary Rust 31 unit + 10 integration tests; legacy-json 14 + 10;
full native decoder/reference comparisons, all-prefix binary truncation and
malformed/unused-row controls; 1567 exact runtime-summary/context/error comparisons;
genuine-world origin and raw/typed mutation rejection; Python 96 tests;
Miri/MiriTests/native build and 71,556-declaration axiom audit, with only the three
permitted axioms. Fresh same-TyCtxt Miri comparisons with **binary** inputs pass
unops, uninitialized-byte-read UB (category and site) and panic catch/unwind;
source, artifact, snapshot fingerprint and memory-event guards remain enabled.
No full upstream UI sweep, fresh caller-location comparison or whole-machine
proof was run for this version.

Two unsuccessful experiments are removed from production source. Reusing full
MIR runtime projections did not materially reduce runtime decoding and was
removed before the locally computed branch summaries. Parallel pure decoder
checks took 29.473 seconds versus 24.471 for the sequential version under the
same four-CPU/four-thread resource allowance; their additional shared-data work
outweighed overlap. That prototype was rejected; the follow-up below changes
work creation and immutable-input ownership before retrying parallelism. Its patches/binaries
and logs remain in ignored scratch evidence.

That revision left repeated full-document walks and binding typed source
results once across decode/lower/preparation as the next priorities. Source equality, constant discovery,
TLS collection and repeated body consistency work remain material. Any replacement
must retain manual/foreign-model rejection, exact diagnostics, compiler identities
and existing proof claims; moving unchanged work into the exporter again is
insufficient. Shared program caches remain explicitly excluded.

## Immutable process input and independent preparation (2026-11-05)

The original, untouched upstream `pass/unops.rs` now finishes below 20 seconds
with binary transport, four available CPUs and three input workers. Final frozen
artifact confirmation samples are **19.587 / 19.819 / 19.572 seconds**, median
**19.587 seconds**, CPU median 23.694 seconds, maximum sampled group RSS 1.900 GB.
This is a warm tool-build result, with fresh Rust compilation/export on every
trial and both cache-valid tool build gates included. Timing starts before the
first gate and ends after the final child exits; post-exit hashing is excluded.
No shared program cache, guest rewrite, omitted std startup or guest budget is
introduced. This is one finite workload, not a universal sub-20-second guarantee.

A preceding three-pair alternating comparison under the same four-CPU allowance
measured d29620f4 at 28.788 / 28.579 / 28.532 seconds versus the new implementation
at 19.840 / 19.829 / 19.673 seconds: medians 28.579 to 19.829, 30.62% shorter.
The final confirmation removes an unused task-mapping helper; it is reported
separately rather than silently mixing artifacts into those pairs. For the
repository's one-CPU/one-Lean-thread comparison, three alternating pairs measure
29.056 / 28.784 / 29.184 versus 23.753 / 23.981 / 24.102 seconds, medians 29.056
to 23.981 (17.46% shorter), CPU medians 28.679 to 23.638, maximum RSS 2.119 to
1.814 GB. Parallel input preparation supplies the additional wall-time reduction;
it does not accelerate guest execution. Same-core steal is recorded per trial
(0.03--0.47 seconds across these groups); cgroup CPU throttling is zero. Phase
medians are independent and must not be added.

All 15 complete outputs across the alternating four-CPU comparison, final
confirmations and one-thread comparison have the historical SHA256
`47a681990447e340c09c71f7a503a9cc8d034ab5019506f3a6826c072a66de67`,
zero readiness obligations, finalized exit 0 and 1361 recorded choice events.
Frozen executables, per-trial counters and raw logs are ignored under
`scratch/perf-direct-checked-graph/`; `source-pairs/parallel-summary.json` and
`source-pairs/validated-summary.json` distinguish the measured groups.

The native one-input path constructs compiler projections once, then uses the
standard Lean `Runtime.markPersistent` GC primitive on the fresh read-only
source graph and completed memos before publishing any tasks. This retains that
input until process exit and avoids repeatedly converting the large graph for
thread sharing. No mutable guest state is pinned. The ordinary pure/library
entry retains normal reclamation; this is not a cache for a later program.
`tools/run.sh` defaults to at most three available input workers, respecting an
explicit `LEAN_NUM_THREADS=1`. The upstream UI harness keeps its serial default
and records an explicit `--input-threads` setting; the guest still reports one CPU.

Independent body/reference checks, source reflexivity and compiler-value
projection run concurrently. The longest whole-runtime check starts first and
uses the original complete cache-miss decoder rather than waiting for the
compiler-value memo. Join points preserve the original first-error order.
Source reflexivity evidence is tied to the exact raw value; record updates clear
it. Lowering computes exact body/source guards in balanced task chunks, carrying
private, dependently indexed certificates. A kernel theorem shows cached guards
leave body lowering unchanged. MIR construction and global ID/span/constant
interning remain serial and ordered. Missing or misplaced certificates fall
back to the historical predicate; they cannot assert readiness.

TLS/constant discovery now accumulates directly into owned output arrays and
folds object trees without temporary lists/flattening. Shared memo setup avoids
constructing paths and index lists for inert nodes. Checked graph dictionaries
compute field classifications/hashes once per name. The exporter fuses its two
vtable/virtual metadata passes, retaining an ordered reference implementation
in tests; an isolated component comparison reduces those passes from 0.609 to
0.362 seconds. These are reductions in work, separate from concurrency.

Completed checks: normal Rust 32 unit + 10 integration; legacy-json 14 + 10;
`tools/check-quick.sh` including Python 96 and source/inventory/fixture integrity;
`tools/check-build.sh` including 47 self-contained runtime checks and the
71,715-declaration axiom audit, with only propext, Quot.sound and Classical.choice.
The full native decoder script passed, including malformed binary controls,
1567 runtime-summary comparisons, ordered source-walk/shared-memo comparisons,
serial/process complete-Core equality for the full genuine binary unops export,
ordered obligations/readiness and lowering/foreign-model rejection. Independently
parsed source-equality and metadata cache fallback/first-error checks also pass.
Fresh same-TyCtxt Miri binary comparisons with three input workers pass unops,
uninitialized-byte-read UB category/site, and panic catch/unwind. Their source,
artifact, snapshot fingerprint and memory-event guards remain enabled.

An earlier decoder check was invalidated by a concurrent build replacing an
OLean. An initial UI unops comparison tripped the memory-event guard while a
large decoder comparison ran concurrently; neither is counted as success.
The decoder was rerun after its build, and all three UI cases were rerun serially
without other heavy checks; all passed. Logs remain under ignored scratch,
including `final-decoder-tests.log`, `final-runtime-build-check.log`,
`final-quick-check.log` and `ui-parallel-final/`. Full UI coverage, fresh caller
location comparison for this revision, and whole-machine safety remain unproved.

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

## Pinned upstream UI sweep

`tools/check-upstream-ui.py` now enumerates the entire pinned pass/fail source
snapshot, including revisions, with explicit profile exclusions (1,118 cases,
809 candidates with the supported settings). See
`tests/upstream_ui/README.md` for the acceptance contract and separate sharded
workflow. A collector rejects incomplete or stale shards independently of
comparison success. Registration and acceptance-oracle unit tests do not establish that
these Rust inputs pass Lean execution.

The [2026-10-26 CI sweep](https://github.com/proofs-rs/lean-miri/actions/runs/40207829366)
finished with **failure**, and inventory coverage was incomplete. Of 809 candidate
cases, the retained results report 604 agreements, 40 Lean timeouts, 33 UB kind/site
mismatches, 45 export failures, 66 other nonpassing outcomes (including unsupported,
process/interpreter failures and pending execution), and 21 missing results.
Shard 27 was interrupted by runner shutdown and did not retain its artifact.
The mismatch causes have not yet been classified as interpreter defects versus
comparison-adapter defects. Do not claim full coverage or count Unsupported,
timeouts, pending execution or missing results as agreement. The full suite runs on pushes to main and manual dispatch only, not on PR
updates; it is not a passing regression gate.

Existing-regression compatibility was checked on 2026-10-26 for the upstream UI
changes (`1bb518eb`). The `Miri`/`MiriTests` build, 47 registered runtime checks,
axiom audit of 69,646 Miri declarations, Python 85 tests and exporter Cargo 9 tests
passed. Existing component comparisons through integer/bool/char operations also
passed, including MachineHooks, retag and Tree Borrows. The standard regression
lane did **not** pass: `tests/integer_cast/run_differential.sh` stopped with exit
124 at its unchanged pinned-reference Miri invocation (180-second timeout), before
Lean comparison. Subsequent checks were attempted separately: immediate, operand,
validity and memory-state/kind checks passed; the input suite was stopped at a
20-minute verification budget while running `DecoderTests.lean`, so later input
checks remain unconfirmed. Eval-core, runtime metadata, arithmetic execution,
calls and globals passed. Frontend timed out at a separate 600-second verification
budget. Extended and connected replay lanes were not rerun in this compatibility
check. No regression was established in the completed checks, but full existing
regression success and the causes of the timeouts remain unconfirmed. These
verification budgets do not change maintained test expectations or interpreter
limits. Detailed local logs are ignored under `scratch/compatibility-check/` and
`scratch/ci/regression/`.

Initial investigation found a shared cost before guest execution: even a std
`miri_start` returning zero pulls thousands of compiler instances through the
exporter's panic/helper/callback query closure. A local prepared export/reference
completed, but does not establish Lean agreement or a bound for larger guests.
Keep the original sources and their std startup; do not hide this cost by
rewriting tests. The opt-in `LEAN_MIRI_TRACE_EXPORT` diagnostic exposes closure
sizes and phases without changing query selection.

The upstream `pass/no_core.rs` reference completed locally, but Lean rejected
its missing structural/compiler obligations before execution, including retained
catalog obligations. This is an unresolved import/bootstrap capability, not a
passed normal-exit comparison. Preserve the strict readiness gate while
investigating the demanded dependencies and absent core language items.
