# Tests and verification

This guide describes the current test layout, what each check establishes, and
how to choose checks after a change. Commands run from the repository root.
Toolchain installation and reference setup are in the
[development guide](../docs/development.md#rust-toolchain-and-reference-setup).
Known validation gaps and outstanding proofs belong in [STATUS](../STATUS.md),
not in this guide. Historical results there are not results for your checkout.

**There is currently no single command that runs every test.**
[`tools/check.sh`](../tools/check.sh) is a broad, explicit list of checks, not a
recursive test runner. Neither `lake build` nor `cargo test` discovers the whole
suite. A passing `check.sh` means its selected checks completed; it does not
include every dedicated decoder, structural, optimization or connected replay
case described below. Self-contained connected proofs are included through
`MiriTests`; the separate connected-proof command additionally typechecks the
retained projection and input-dependent graph harnesses.

Historical schema-11/12 inputs use explicit test-only adapters
[`LegacyFixture.lean`](../MiriTests/Input/LegacyFixture.lean) and
[`legacy_fixture_schema.py`](../tools/legacy_fixture_schema.py); production
readers accept only schema 13. These adapters preserve retained fixture bytes on
disk. Their unwind, drop-definition and generic-prefix seeds are hypothetical representatives
preserving historical answers, not recovered rustc material. Such replay is
component regression evidence, with no new producer, ABI, drop or generic-rebase
correspondence claim. Tests asserting actual raw materials require fresh exports;
the genuine differential drivers use category parsers or independently fresh
baseline and candidate exports.

Source compiler-query comparisons also have dedicated drivers in `tools/`:
`check-dynamic-type-hash.sh`, `check-pattern-type-hash.sh`,
`check-vtable-method-slots.sh`, `check-vtable-final-instances.sh` and
`check-fn-pointer-hrtb-shims.sh`. They compare fresh exports with independent
pinned-rustc queries and exercise their stated malformed-source controls.
Use an exporter built from the same source revision and the pinned environment;
the FnPtr driver requires its immutable path in `EXPORTER_BIN`. These finite
comparisons do not establish general query equivalence. Run their build stages
before starting other fixture readers; `*_SKIP_BUILD=1` is appropriate only after
a coordinated complete rebuild of changed schemas and their dependents.

## Self-contained Lean checks: MiriTests

Self-contained theorem examples and assertions live in [`MiriTests/`](../MiriTests/),
grouped by feature. Rust comparisons, fresh/saved input harnesses, fixtures and
profiling remain under `tests/` with their drivers.

```bash
lake build MiriTests
lake exe miri_tests
lake exe miri_tests --list
lake exe miri_tests --case MiriTests.Native.BytesOwnership
```

The library explicitly includes all `MiriTests` submodules. Its root
[`MiriTests.lean`](../MiriTests.lean) imports declaration/proof modules;
[`MiriTests/AxiomAudit.lean`](../MiriTests/AxiomAudit.lean) audits those imports and
the interpreter. Runtime files retain independent `main` declarations and are
built as separate modules, not imported together into that root. Do not interpret
this audit as an audit of every runtime harness's declaration environment.

The runtime registry is [`RuntimeChecks.lean`](../MiriTests/RuntimeChecks.lean).
The runner invokes a fresh `lake env lean` process per entry, adding `--run` for
files with a `main`. It reruns source `#eval` assertions even with warm Lake caches,
reports the failing path and propagates nonzero exit status. It stops at the first
failure. Process isolation also prevents test-local instances and global names
from leaking between runtime cases. Run from the repository root with the pinned
Lean environment on PATH. This uses Lean's source execution, not a native build
of the whole interpreter.

Add declaration/proof modules to the root imports so they participate in its
axiom audit. Add executable assertions to the runtime registry, selecting whether
to run `main`. Build success alone does not execute a `main`; cached builds do not
rerun `#eval`. `check-build.sh` and `check.sh` invoke both the library and runtime
runner. Existing focused scripts retain their relevant migrated cases.

The feature folders include `ABI`, `Aggregate`, `Allocation`, `AtomicScalar`,
`Connected/Proofs`, `Connected/Focused`, `Constant`, `ControlFlow`, `DataRace`,
`FloatOps`, `FunctionPointers`, `Input`, `LocalAccess`, `MachineHooks`,
`Memory112`, `MemoryState`, `Native`, `Place`, `Projection`, `Regression`, `RunLoop`,
`Rvalue`, `Safety`, `Scalar`, `ScalarOps`, `Scheduling`, `Step`, `TreeBorrows` and
`Validity`, as well as `Cast`. They mirror existing feature names; migration does
not change the assertions or turn finite checks into general proofs.

## What is being checked?

The main behavior pipeline is:

```text
Rust source
  -> pinned rustc + exporter: MIR, types, compiler queries and allocations
  -> Lean decoder, lowering and preparation
  -> shared Lean interpreter
  -> observable result, expected UB, or another explicitly classified outcome
```

Checks exercise different parts of that pipeline:

| Kind | Question | Limit of the evidence |
| --- | --- | --- |
| Lean typechecking | Are the definitions and theorem declarations accepted? | Well-typed interpreter code alone does not prove correspondence with Rust or Miri. |
| Kernel-checked proofs | Does a stated property follow from the definitions and assumptions? | Covers the theorem's scope and assumptions, not automatically input generation, host behavior or the whole machine. |
| Executable assertions | Does this concrete input produce the expected result or error? | Finite examples; often also checks failure order and retained state. |
| Component differential tests | Does a Lean operation agree with a pinned reference operation on selected inputs? | References may be extracted/adapted Rust bodies with fixture leaves, rather than a complete Miri run. |
| Exporter/consumer contracts | Does genuine compiler output satisfy the schema, and does Lean interpret its identities and queries correctly? | Successful decoding/preparation is not successful guest execution. |
| End-to-end comparisons | Does an exported Rust program run with the expected observations and terminal outcome? | Finite programs and choices, with the reference contract specified by the harness. |
| Source audits | Are pins, links, inventories and recorded obligations consistent? | Bookkeeping and source integrity, not semantic completeness. |
| Profiling | How much time/memory does a fixed execution consume? | A measurement is not a correctness assertion or a general speedup claim. |

### Why test a Lean implementation?

Lean verifies the propositions actually stated. It does not infer that an
interpreter implements Rust correctly merely because it is written in Lean.
A proof about a memory helper can quantify over all inputs satisfying its
preconditions, while leaving open whether real imported programs establish those
preconditions or whether the helper models the intended upstream rule.
Tests cover concrete port correspondence, input contracts, assembled execution
and external boundaries. Proofs and tests therefore serve different purposes.

A `.lean` file can contain both proofs and executable checks:

- `lake env lean FILE.lean` elaborates the file and also executes its `#eval`
  commands. It does not call a declared `main` automatically.
- `lake env lean --run FILE.lean ARG...` also runs `main` with the arguments.
- `lake build` checks its configured targets; it does not discover arbitrary
  files below `tests/`. The default `MiriTests` target in
  [lakefile.lean](../lakefile.lean) explicitly includes `MiriTests` submodules.

Accepted proof axioms are `propext`, `Quot.sound` and `Classical.choice`.
Executable assertions are separate from proofs; `native_decide` and unchecked
verification axioms are prohibited by [AGENTS](../AGENTS.md).

## Main check entry points

The last column describes inclusion in `tools/check.sh`, including indirect
calls. It does not describe which checks ought to be included in a future runner.
Scripts are the authority for individual cases and build behavior.

| Command | Purpose and input | Included in `check.sh`? |
| --- | --- | --- |
| `bash tools/check-quick.sh` | Source pins/audits, Python tool tests, obligation inventory, saved-fixture hashes. No Lean or exporter build; audit generation needs the Rust analyzer. | Much of the audit/Python work overlaps, but this script and its two fixture hash-manifest checks are not called. |
| `bash tools/check-build.sh` | Build library, self-contained tests, frontend and choice policy; run self-contained assertions and audit axioms. | Its build, runtime and axiom work overlaps; this script is not called. |
| `bash tools/check-decoder.sh` | Strict success/failure boundaries, 16 saved-expectation cases and 4 shared-ID checks; unit mutations with exact malformed-field and reference diagnostics. | No. Other decoder tests run, but these dedicated checks do not. |
| `bash tools/check-structural-regressions.sh` | Context/provider/primitive rebinding, maps, zero width, thread-clock reuse, typed descriptor destruction and collection QA; proofs, `#eval` and runtime assertions. Uses adapted pinned unit inputs or no input. | Migrated self-contained cases are built/run through `MiriTests`; input-dependent cases are not included as a suite. |
| `bash tools/check-performance-regressions.sh` | Finite equivalence/error-order/state-retention checks for indexes, ABI/backtrace caches, decoder caching, profiles and imported allocations. | Includes migrated self-contained cases and some input/memory overlap; dedicated input-driven parity cases still require this suite. |
| `bash tools/check-connected-proofs.sh` | Build/audit `MiriTests` (including connected component proofs) and typecheck the retained SC projection and graph runner. | Component proofs are included; graph-runner typechecking is separate. |
| `bash tools/check.sh` | Source audits, selected component tests, exporter contracts and fresh producer-to-consumer/execution checks. | This is the broad regression entry point, not an all-tests command. |

The dedicated decoder mutations use `input/fixtures/strict-unit.json`, a
synthetic document for schema and identity checks. It is not evidence
of a Rust execution. Retained historical exporter files remain unchanged; their
wire formats are not compatibility inputs for the current importer. Fresh
exporter and frontend checks exercise current producer-to-consumer agreement.

**“Performance regressions” here means preserving behavior through optimizations.**
That script does not use speed thresholds to decide success.

After setup, run the relevant entry points separately, for example:

```bash
mkdir -p scratch/logs
bash tools/check-quick.sh > scratch/logs/quick.log 2>&1
bash tools/check-build.sh > scratch/logs/build.log 2>&1
bash tools/check-decoder.sh > scratch/logs/decoder.log 2>&1
bash tools/check-structural-regressions.sh > scratch/logs/structural.log 2>&1
bash tools/check-performance-regressions.sh > scratch/logs/optimization.log 2>&1
bash tools/check-connected-proofs.sh > scratch/logs/proofs.log 2>&1
```

Use new log names for subsequent attempts. These commands are not a substitute
for the connected/fresh checks or standalone tests relevant to a change.

### What `check.sh` actually runs

The ordered list is maintained in [the script](../tools/check.sh). Its phases are:

1. Generate/check source audits, run Python unittest discovery under `tests/`,
   and run the Rust source analyzer's Cargo tests.
2. Build Lean defaults (including all `MiriTests` modules), run the self-contained
   runtime registry, build frontend and choice policy; audit axioms and source links.
3. Explicitly run selected control-flow, call/stack, layout/value, memory,
   Tree Borrows, atomic, synchronization and data-structure tests.
4. Run pinned `cargo test --locked --offline --manifest-path exporter/Cargo.toml`
   for exporter Rust/Python unit tests, all four fixture scripts and four producer checks. See the
   [exporter test instructions](../exporter/README.md#tests).
5. Run `input/run.sh`, `eval_core/run.sh`, `frontend/run.sh`,
   `runtime_metadata/run.py` and `execution/run{,_calls,_globals}.py`.
6. Compare the extracted obligation inventory with the checked-in fixture.

The input check freshly exports Rust, exercises typed-table decoding, lowering,
preparation and selected allocator-world metadata. The frontend check imports
fresh JSON into Lean constants. Runtime-metadata checks connect fresh compiler
queries to Lean providers. Execution checks compare selected arithmetic, calls
and globals with pinned Miri. Eval-core's six checks use three hash-checked
compiler exports mechanically projected to schema 11. The projection removes unused
diagnostic fields and checks every retained payload exactly. The preparation helper preserves their current
decompressed bytes exactly; the projection manifest pins both original and retained expanded data.

The script uses `set -euo pipefail`: a failure stops it and later phases remain
unexecuted. A timeout is not a pass. Python discovery does not recursively run
all `.py`, `.sh` or `.lean` files: subdirectories without discovery packages and
files outside its naming rules require explicit invocation. In particular,
`exporter/tests/` is outside its discovery root.

## Connected execution: saved replay versus fresh export

“Connected” tests run compiler-produced input through the assembled interpreter.
They complement local component comparisons. See the
[connected guide](connected/README.md) for contracts and harness details.
None of these top-level commands is called by `tools/check.sh`:

| Command | Checks |
| --- | --- |
| `python3 tools/check-connected.py` | Run canonical12 genuine exports (11 saved, DST fresh): protectors, races, DST, TLS, ordinary main, upcasts, SC and Relaxed. Nine normal and three expected-UB cases. |
| `python3 tools/check-connected.py --case 198-sc-base` | Select one canonical case; `--case` can be repeated. |
| `python3 tools/check-connected.py --ordering` | Four matched SC/weak controls, choice domains, typed prefixes and operation/scheduler order. |
| `python3 tools/check-sc-schedules.py` | SC diagnostic seeds 0–11 and rejection of truncated/out-of-support/missing-post-step logs. |
| `python3 tools/check-connected.py --large-tb` | Fresh larger Rust export; assert the expected Frozen-tag write UB. |
| `python3 tests/connected/compare_selector.py` | Finite comparison of choice selection with extracted upstream code; does not execute the whole Miri interpreter. |

Fifteen cases use stored same-TyCtxt reference observations and schema-11 payload
projections of the original compiler data. Sidecars retain the original byte binding
under `wire_projection`; no new Miri execution is claimed for that transformation.
The DST and large Tree Borrows cases generate fresh exports and same-TyCtxt
Miri references in CI from tracked Rust sources, unchanged flags and exactly
reviewed guest configuration/argv0. Their Lean assertions and choice tapes
remain fixed. Replay therefore needs the pinned Rust/sysroot and reference
exporter build; these two cases no longer compare immutable saved allocation
histories. Their historical archives are not CI inputs. The 17-case Lean connected run
passes under schema 7 with the unchanged expected outcomes. The full CI matrix
remains unexecuted.
Fresh generation is a separate operation via
[tools/export-connected.py](../tools/export-connected.py).
Changing exporter/query collection requires fresh checks as well as replay:
unchanged saved JSON cannot expose a new producer defect.

Some cases require minutes and about 15 GB of memory. `--timeout SECONDS` controls
the replay's per-case limit (default 900); expiration is failure, not Unsupported
or safe execution. Diagnostic seeds are a finite sample, not all schedules.
The proof script only typechecks graph machinery; it does not complete a graph
exploration or establish whole-machine safety.

### Additional fresh comparisons

These also have independent entry points. Their setup and exact invocations are
in [repro/README.md](repro/README.md); output arguments should name new locations
under ignored `scratch/`.

| Entry point | Purpose / extra prerequisites |
| --- | --- |
| `python3 tools/check-powi-zero.py scratch/powi-zero-new` | Fresh same-prepared-TyCtxt comparison with Miri; 16 f32/f64 exponent-zero exact result-bit assertions. Reference-feature exporter, MIR sysroot and Lean dependencies required. |
| `python3 tools/check-math-nohost.py scratch/math-nohost-new` | Fresh sin(1)/cos(0) controls with/without math host; checks exact capability Unsupported and rejects wrong terminal expectations. Requires reference-feature exporter and sysroot. |
| `tools/check-vtable-erasure.py` | Fresh query/predicate/vtable allocation joins, including HRTB/upcast/static and separately built cross-crate metadata controls. Also runs `input/DecoderDirectLockstep2026.lean`: direct inputs must decode; with `--require-lockstep`, genuine upcast answers are required and restoring only their obsolete envelopes must reject the exact upcast evidence. Other controls require absent lockstep rows. Takes source/output and expectation arguments; identity controls are not nonidentity witnesses. |
| `tools/check-timezone.py` | Fresh localtime_r guest comparison with standalone pinned Miri in a separate TyCtxt; requires matching libc rlib, reference build record, sysroot and ordinary exporter. Takes output and `--libc` arguments. |

[connected/focused/](connected/focused/README.md) contains additional atomic
handoff/fence, pthread race and backtrace harnesses. These require genuine fresh
inputs and, for the atomic/race harnesses, an explicit expected outcome argument.
The no-input KeyedArray and MemoryState QA files moved to `MiriTests/Connected/Focused/`
and are called by both the runtime registry and structural regression script; do not classify the whole directory
as unexecuted merely because guest harnesses need manual setup.

## Directory map

This maps feature areas; self-contained Lean files have moved to matching
`MiriTests/` folders while their external drivers and inputs remain under `tests/`.
Some listed feature directories now exist only under `MiriTests/`. A group
is an explanation, not a promise that one runner executes every file in it.
Proofs, assertions, source adapters and fixtures may coexist within a feature.
Names below follow the original feature groups; `lean` examples are now in
`MiriTests/Safety/`, with the audit driver at `MiriTests/AxiomAudit.lean`.

| Area | Feature names | Contents |
| --- | --- | --- |
| Execution control | `step`, `control_flow`, `run_loop`, `call`, `stack` | MIR transitions, dispatch, calls/returns, lifecycle and safety examples. |
| Types and places | `abi`, `layout`, `dynamic_layout`, `place`, `projection` | ABI/layout, dynamically sized values, addresses and field projection. |
| Values and expressions | `aggregate`, `cast`, `constant`, `discriminant`, `float_ops`, `immediate`, `integer_cast`, `integer_ops`, `local_access`, `operand`, `rvalue`, `scalar`, `scalar_ops`, `validity` | Value construction, arithmetic, conversions, constants and validity checks. |
| Memory and borrowing | `allocation`, `allocation_access`, `init_mask`, `machine_hooks`, `memory112`, `memory_kind`, `memory_operand`, `memory_state`, `pointer`, `tree_borrows` | Allocation/access, initialization, provenance-sensitive operations and borrowing. `memory112` is a historical test name, not a separate subsystem API. |
| Internal collections/addresses | `alloc_addresses`, `dedup_range_map`, `provenance_map`, `range_object_map` | Address allocation and range-map operations. |
| Concurrency | `atomic_scalar`, `data_race`, `scheduling`, `sync`, `vector_clock`, `weak_memory` | Atomic results, ordering, clocks, scheduling, synchronization and race detection. |
| Compiler input | `producer`, `input`, `query_demand`, `runtime_metadata`, `frontend` | Producer evidence, decoding, lowering, preparation, query demand and constant import. `input/` also contains cache regressions and profiling harnesses. |
| Assembled execution | `eval_core`, `execution`, `connected` | Unit execution fixtures, fresh execution comparisons, saved connected replays and local connected proofs. |
| Specialized/external boundaries | `aes`, `intrinsic_float`, `random_memory`, `native`, `function_pointers` | AES/APFloat helpers, RNG/error sequencing, host-byte ownership, persistent function/vtable IDs. |
| Cross-cutting checks | `regression`, `lean` | Additional regression cases; safety-interface examples and axiom audit. |
| Inputs and observations | `fixtures`, `repro`, `reference_programs` | Obligation snapshot, Rust reproductions and reference-only observations. |

Top-level `test_*.py` files test development tools: audit/coverage/ledger handling,
source pins and lint, vtable trace consumption, and ordinary body/progress/measure
utilities. They are run by unittest discovery in quick/full checks. They do not
collect every feature test in the directories above.

### Exporter tests live outside `tests/`

[exporter/tests/](../exporter/tests/) holds Python schema/contract validators,
transport unit tests and the Cargo integration test entry point.
[exporter/fixtures/](../exporter/fixtures/) holds Rust inputs and small Cargo
projects. The allocator-world Rust fixtures shared by exporter and Lean input
checks live under `tests/fixtures/`.

Pinned `cargo test --locked --offline --manifest-path exporter/Cargo.toml` runs
Rust unit tests, Python unittest discovery, the four top-level shell fixture
scripts and four producer checks: settings/artifact hashes, primitive ranges,
function/vtable AllocId crosswalks, and static/TypeId crosswalks. `tools/check.sh`
uses this entry point. See the [exporter guide](../exporter/README.md#tests) for
setup, focused invocations and standalone scripts.

`tests/producer/primitive_ranges.py` retains the Lean decoder/runtime boundary
checks and obtains its input from the exporter-owned primitive-range check.
`tests/input/run.sh` uses the shared allocator-world fixtures in `tests/fixtures/`
and the exporter validators before testing their Lean consumers. These consumer
checks remain separate from Cargo's exporter suite.

## Standalone checks that need explicit selection

The following checks need explicit selection unless marked as included below.
This is a selection guide, not a claim that these are obsolete or an exhaustive
list of every uninvoked Lean declaration. Inspect the relevant feature directory
when changing it.

| Check / invocation | What it adds |
| --- | --- |
| `bash tools/check-fn-trait-output.sh` | Independent pinned Fn/FnMut/FnOnce candidate and Output normalization comparisons, including genuine standard-library closure material selected by `FN_TRAIT_STD_SOURCE`. Requires the pinned exporter, source sysroot and coherent Lean build; it does not establish general trait selection. |
| `bash tools/check-fn-trait-boundaries.sh` | Genuine nested-FnPtr tuple comparisons retain all signature fields despite JSON key order; unsafe-inner-signature controls reject. An actual async closure's successful compiler FnOnce candidate must remain explicitly Unsupported in the bounded Lean provider. |
| `bash tools/check-iterator-conditional.sh STD_FIXTURE.json` | Compare the genuine IntoIterator signature and three Iterator goals with the pinned compiler, including the exact selected physical impl and a corrupted-impl oracle. Known non-coroutine heads exclude only compiler coroutine candidates; unresolved/dynamic/coroutine goals remain unsupported. |
| `bash tools/check-initial-profile-rejection.sh VALID_DOCUMENT.json` | Four malformed/present-field controls added to an independently accepted current document require the legacy public decoder to reject the separate initial-allocation/CTFE profile explicitly. Requires a built decoder; it does not validate the dedicated initial-profile execution path. |
| `lake env lean --run tests/run_loop/HostStdioReplay.lean` | Pure typed stdio replay checks: exact requests, response bounds, first-pending cleanup retention, missing-state rejection and unchanged choice/RNG state. Included in structural regressions; it supplies no host IO capability. |
| `lake env lean --run tests/run_loop/NativeStdioProtocol.lean` | Pure control-option and JSON framing checks, including escaped spoofed output. Included in structural regressions after the runner module build. |
| `flock /tmp/lean-miri-ci-guest.lock python3 tests/stdio/check.py --output scratch/stdio-new` | Fresh pinned-reference/guest comparison for explicit stdio: repeated writes, binary bytes, spoofed result lines and preserved muted ordinary descriptors. Requires coherent reference exporter/native runner; unsupported and timeout outcomes fail. |
| `python3 tests/intrinsic_float/source_compare.py` | Finite intrinsic helper comparison against pinned APFloat: FMA, rounding, min/max and NaN handling. Requires its Rust oracle dependencies. |
| `python3 tests/aes/source_compare.py` | Compare pinned AES fixslice bodies; requires offline vendor configuration at `scratch/cargo-vendor.toml` and matching crates. |
| `flock /tmp/lean-miri-ci-guest.lock python3 tests/x86_pack/check.py --output scratch/x86-pack-new` | Fresh pinned-reference/guest comparisons for 128/256/512-bit signed and unsigned saturation boundaries and 128-bit chunk/lane order; requires a reference-feature exporter and matching native runner. Unsupported and timeouts fail the check. |
| `python3 tests/random_memory/source_compare.py` | Extracted gen_random outer-body ordering and failure propagation; RNG/host/write leaves are fixtures. |
| `python3 tests/producer/primitive_ranges.py` | Genuine u128/niche metadata and Lean decoder boundaries; requires built debug exporter and MIR sysroot. |
| `cargo +miri-exporter-8144389c895d test --manifest-path exporter/Cargo.toml --locked --offline` | Rust/Python exporter tests, four fixture scripts and four producer checks; included in `check.sh`. Requires pinned toolchain, MIR sysroot and offline dependencies. |
| `python3 -m unittest discover -s exporter/tests -p 'test_*.py' -v` | Python typed-table schema loader tests, outside the main discovery root. |
| `lake env lean MiriTests/Cast/Typed.lean` | Cast dispatcher, check order and size-mismatch cases; now included in `lake build MiriTests`. |
| `lake env lean --run MiriTests/Native/BytesOwnership.lean` | Included in `lake exe miri_tests`: host-byte ownership, release and copy-failure cleanup using fixture hosts. “Native” here names the boundary, not an execution mode. |
| `python3 tests/scheduling/test_source_prefix.py` | Extracted scheduler service prefix with fixture leaves, and `Stateful.lean` proof examples. |
| `MiriTests/FunctionPointers/*.lean` | Self-contained persistent reservation assertions are included in the runtime registry. |
| `tests/query_demand/make_cases.py` + `CatalogRoles.lean` | Generate mutations from fresh compiler evidence, then run readiness/obligation/provider assertions. Native-signature and TLS cases run in the fresh CI lane; the existing missing TLS consumer provider branch remains a visible failure. |

`exporter/tests/check_runtime_type_closure.py` checks a supplied compiler export.
The fresh CI lane exports its fixture and runs the helper. See
[CI coverage](../tools/ci/README.md) and the
[upstream UI contract](upstream_ui/README.md) for scheduled entry points.

## Choosing checks after a change

A green `check.sh` is useful broad regression evidence, but is insufficient if
related tests live outside its call graph. Select checks by the changed behavior,
not just the implementation filename. Shared decoder/memory/choice changes can
affect several rows below.

| Change | Checks to select in addition to broad regression coverage |
| --- | --- |
| Export schema, rustc query collection, roots or allocation identities | Exporter fixtures and transport tests; producer tests; input/frontend/runtime-metadata checks; fresh execution or fresh connected cases. Saved replay alone cannot test a changed exporter. |
| Typed pool IDs or validation | Dedicated decoder suite, relevant input checks, pool-reference tests and query-demand rejection cases. |
| Lowering, compiler providers, primitive binding or preparation | Structural suite, relevant input/runtime-metadata cases, optimization suite for indexes/caches, and an assembled execution exercising the changed path. |
| Indexes, memoization, profiles, rollback or retained state | Optimization suite plus the relevant feature tests and end-to-end control; use the profiling protocol separately for speed claims. |
| Arithmetic, casts, intrinsics or AES | Relevant component runner/Lean assertions; standalone cast/APFloat/AES checks as applicable; fresh guest comparison when dispatch/input integration changes. |
| Memory, pointer or Tree Borrows semantics | Relevant component comparisons; structural/optimization checks if affected; canonical protector/DST/upcast cases and large-TB when applicable. |
| Atomics, weak memory, races, synchronization or scheduling | Relevant component tests, canonical connected cases, ordering controls, SC diagnostic seeds, scheduling prefix and relevant focused guests. Finite seeds do not prove all schedules. |
| Host bytes, RNG, native math or timezone | Standalone ownership/RNG/native boundary checks and the corresponding fresh math/timezone guest checks. |
| Theorem statements, safety definitions or dependencies | Rebuild affected proofs, build/axiom check and connected proof suite if affected. Check theorem assumptions as well as executable behavior. |
| Audit or execution/measurement tools | Top-level Python tests/quick checks, analyzer Cargo tests where relevant, and the affected command's behavior. |

For a broad interpreter refactor, run the separate decoder, structural,
optimization, connected-proof and connected replay suites as well as `check.sh`,
then select fresh/standalone checks for affected paths. This is a coverage
selection policy, not an existing all-tests runner or a proof of completeness.

## Setup, data and result interpretation

Use the pinned toolchains and environment from the development guide. Some
component adapters also explicitly use the repository's stable Rust installation;
read their scripts for dependencies. Offline Cargo invocations require previously
fetched or vendored crates. A setup failure means the test did not complete.
Serialize primary Lake writers with `/tmp/lean-miri-lake-build.lock`; do not wrap
scripts already holding that lock in another `flock`, and do not share writable
`.lake` artifacts between checkouts. `check.sh` itself is not a global lock wrapper.

Keep these artifacts distinct:

- `repro/` Rust files are inputs, not automatically runnable tests.
- `fixtures/` directories hold input bytes, expected results, reference diagnostics
  and hashes. A hash check proves integrity, not interpreter agreement.
- `build_id_fixtures.py`, `tools/prepare-regression-inputs.py` and
  `tools/export-connected.py` generate or transform input; their success alone
  does not establish guest correctness.
- `tools/setup-*.sh` and `tools/build-*.sh` prepare dependencies and executables.
- `tools/run.sh` executes ordinary input without test-specific expected-result
  assertions. `tools/measure.py` and profiling harnesses measure execution; see
  [PROFILING](../tools/PROFILING.md).
- `reference_programs/run.py` collects observations from pinned Miri only; it does
  not compare them with Lean.

Expected-UB test harnesses can exit zero because they successfully recognized the
expected UB. Conversely, Unsupported, fuel exhaustion, pending execution, an
interpreter error or a failed process must not be counted as safe execution.
An absent-host test may deliberately assert a particular Unsupported outcome;
that validates capability handling, not successful guest execution.

Report the revision, commands, completed outcomes, failures/timeouts and checks
not executed. Normal termination for selected programs/seeds is finite evidence.
UB freedom requires excluding UB on every reachable permitted finite prefix;
local proofs, open graph exploration and source inventories do not establish that
whole-machine claim.

`bash tools/check-lowering-reader.sh [INPUT.json ...]` checks source paths and
compiler pool IDs across lowering for root, instance and promoted bodies.
The default input is the fixed empty-function fixture.

`tools/check-extended-source-mir.py --exporter EXPORTER --oracle ORACLE
--sysroot SYSROOT --output scratch/extended-source-mir [--lake LAKE]` exports
fresh extended-source and no-resume inputs with the pinned producer. Compile
`tools/extended-source-mir-oracle.rs` with the pinned exporter rustc to obtain
ORACLE. The runner replays the fresh document's exact `input_settings.rustc_args`
through that independent oracle, including `-Zmir-preserve-ub`, and records the
command and selection indices in `oracle-scope-manifest.json`.

The full oracle covers 42 complete normalized MIR bodies, 35 raw-source rejection
controls and four FnDef interface controls. The World comparison covers the 41
unchanged oracle rows whose physical definitions the producer retains, including
12 persistent call callbacks and missing/ambiguous-source rejection. The remaining
`raw_pointer` row must reject for an absent physical definition; it is expected
Unsupported, not a successful World comparison. `--lake` runs these focused Lean
checks and the two no-resume layout controls without building artifacts. Run only
after primary writers release their barrier; export/oracle capture alone does not
establish any Lean comparison result.

`tools/check-annotated-source-mir.py --exporter EXPORTER --oracle ORACLE
--sysroot SYSROOT --output scratch/annotated-source-mir [--lake LAKE]` uses an
ORACLE compiled from `tools/annotated-source-mir-oracle.rs`. It replays exact
producer flags and captures eight complete normalized bodies with preserved
annotation indices and spans, eight raw-source rejection controls, and five
malformed annotation decoder controls. Runtime annotations explicitly retain the
post-borrowck cleared-table marker; stale indices are not dereferenced into that
empty table. FnDef-to-FnPtr reification remains unsupported in this source grammar.

`tools/check-source-trait-call.py --exporter EXPORTER --oracle ORACLE
--sysroot SYSROOT --output scratch/source-trait-call [--lake LAKE]
[--runner NATIVE_RUNNER]` uses an ORACLE compiled from
`tools/source-trait-call-oracle.rs`. It preserves a genuine method-syntax
associated FnDef declaration and compares its selected physical impl with pinned
rustc. Default export retains the nongeneric impl as an independent actual root;
root-only export deliberately tests missing impl source. This is not general
source impl-body discovery. Annotated UFCS call operands remain unsupported.
Optional Lean checks compare the complete caller body and resolve its selected
raw impl body; the optional existing runner must report finalized exit zero.
Neither option builds primary artifacts.


## Virtual ABI source queries

After building the current Lean library, run the finite pinned comparisons with
an explicit sealed default exporter and its separately built FullLayout oracle:

```sh
python3 tools/check-virtual-abi.py \
  --exporter "$MIRI_SEALED_EXPORTER" \
  --manifest "$MIRI_SEALED_EXPORTER_MANIFEST" \
  --oracle-exporter "$VIRTUAL_ABI_ORACLE" \
  --oracle-manifest "$VIRTUAL_ABI_ORACLE_MANIFEST" \
  --output scratch/virtual-abi-unique-run
```

The oracle seal must identify its actual receiver FullLayout adapter. The
checker invokes both producers with the same Rust flags, records input/binary
hashes, audits direct/catalog/identity query traces, and compares complete FnAbi
values for 51 distinct method/policy cases. Separate pinned rustc drivers observe
receiver lowering and field size/alignment independently. The checker does not
build the primary Lean tree.

The query worlds remove imported FnAbi catalogs and instance/body stores. They
also remove projection, boolean and ADT fact rows and poison cached closed ADT
field TypeIds while retaining raw definition field expressions. This checks that
logical field substitution and layout demands use the source providers.

`WorldVirtualInstanceAbi` now includes the tracked method: its source
PanicLocation argument is appended after ordinary arguments without increasing
fixedCount. `WorldVirtualReceiverAbi` covers by-value dyn and one/two transparent
raw-pointer wrappers. `WorldTrackedVirtualAbi` checks missing/wrong caller type,
session and extras. Novel and positive-auto checkers retain their independent
oracle comparisons with the same cache removal. Caller source guards reject a
primitive recipe assigned to the Location ADT, a missing raw field and a missing
raw lang-item identity. Wrong logical receivers, non-null/alias attributes,
caller lifetimes and fixedCount must fail complete comparisons.

Three wrappers remain an explicit artificial capability limit; the rustc oracle
still supports that receiver. Other newtypes, source upcasts and unsupported
caller-layout dependencies remain residual. These are finite x86_64/AS0 API
comparisons; they do not establish universal ABI correctness, raw dynamic MIR
admission, new-receiver guest execution or whole-machine UB freedom.
