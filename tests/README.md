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
| `bash tools/check-decoder.sh` | 16 saved-expectation decoder cases plus 4 shared-ID checks; generated mutations and retained genuine schema-3 exports. | No. Other decoder tests run, but these dedicated checks do not. |
| `bash tools/check-structural-regressions.sh` | Context/provider/primitive rebinding, maps, zero width, thread-clock reuse and collection QA; proofs, `#eval` and runtime assertions. Uses adapted pinned unit inputs or no input. | Migrated self-contained cases are built/run through `MiriTests`; input-dependent cases are not included as a suite. |
| `bash tools/check-performance-regressions.sh` | Finite equivalence/error-order/state-retention checks for indexes, ABI/backtrace caches, decoder caching, profiles and imported allocations. | Includes migrated self-contained cases and some input/memory overlap; dedicated input-driven parity cases still require this suite. |
| `bash tools/check-connected-proofs.sh` | Build/audit `MiriTests` (including connected component proofs) and typecheck the retained SC projection and graph runner. | Component proofs are included; graph-runner typechecking is separate. |
| `bash tools/check.sh` | Source audits, selected component tests, exporter contracts and fresh producer-to-consumer/execution checks. | This is the broad regression entry point, not an all-tests command. |

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

The input check freshly exports Rust, exercises full/runtime decoding, lowering,
preparation and selected allocator-world metadata. The frontend check imports
fresh JSON into Lean constants. Runtime-metadata checks connect fresh compiler
queries to Lean providers. Execution checks compare selected arithmetic, calls
and globals with pinned Miri. Eval-core's six checks instead use hash-checked old
exports converted into schema-3 **unit fixtures**; they are not fresh exports.

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
| `python3 tools/check-connected.py` | Replay canonical12 saved genuine exports: protectors, races, DST, TLS, ordinary main, upcasts, SC and Relaxed. Nine normal and three expected-UB cases. |
| `python3 tools/check-connected.py --case 198-sc-base` | Select one canonical case; `--case` can be repeated. |
| `python3 tools/check-connected.py --ordering` | Four matched SC/weak controls, choice domains, typed prefixes and operation/scheduler order. |
| `python3 tools/check-sc-schedules.py` | SC diagnostic seeds 0–11 and rejection of truncated/out-of-support/missing-post-step logs. |
| `python3 tools/check-connected.py --large-tb` | Larger saved Rust export; assert the expected Frozen-tag write UB. |
| `python3 tests/connected/compare_selector.py` | Finite comparison of choice selection with extracted upstream code; does not execute the whole Miri interpreter. |

Replay uses stored reference observations; it does not rerun rustc/exporter or
reference Miri. The references specify the same prepared TyCtxt after snapshot
capture, not vanilla Miri's allocation-ID history. Fresh generation is a separate
operation via [tools/export-connected.py](../tools/export-connected.py).
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
| `tools/check-vtable-erasure.py` | Fresh query/predicate/vtable allocation joins, including HRTB/upcast/static and separately built cross-crate metadata controls. Takes source/output and expectation arguments; identity controls are not nonidentity witnesses. |
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
projects, including the fixtures shared with Lean input checks.

Pinned `cargo test --locked --offline --manifest-path exporter/Cargo.toml` runs
Rust unit tests, Python unittest discovery, the four top-level shell fixture
scripts and four producer checks: settings/artifact hashes, primitive ranges,
function/vtable AllocId crosswalks, and static/TypeId crosswalks. `tools/check.sh`
uses this entry point. See the [exporter guide](../exporter/README.md#tests) for
setup, focused invocations and standalone scripts.

`tests/producer/primitive_ranges.py` retains the Lean decoder/runtime boundary
checks and obtains its input from the exporter-owned primitive-range check.
`tests/input/run.sh` reuses the exporter-owned allocator-world fixtures and
validators before testing their Lean consumers. These consumer checks remain
separate from Cargo's exporter suite.

## Standalone checks that need explicit selection

The following checks need explicit selection unless marked as included below.
This is a selection guide, not a claim that these are obsolete or an exhaustive
list of every uninvoked Lean declaration. Inspect the relevant feature directory
when changing it.

| Check / invocation | What it adds |
| --- | --- |
| `python3 tests/intrinsic_float/source_compare.py` | Finite intrinsic helper comparison against pinned APFloat: FMA, rounding, min/max and NaN handling. Requires its Rust oracle dependencies. |
| `python3 tests/aes/source_compare.py` | Compare pinned AES fixslice bodies; requires offline vendor configuration at `scratch/cargo-vendor.toml` and matching crates. |
| `python3 tests/random_memory/source_compare.py` | Extracted gen_random outer-body ordering and failure propagation; RNG/host/write leaves are fixtures. |
| `python3 tests/producer/primitive_ranges.py` | Genuine u128/niche metadata and Lean decoder boundaries; requires built debug exporter and MIR sysroot. |
| `cargo +miri-exporter-8144389c895d test --manifest-path exporter/Cargo.toml --locked --offline` | Rust/Python exporter tests, four fixture scripts and four producer checks; included in `check.sh`. Requires pinned toolchain, MIR sysroot and offline dependencies. |
| `python3 -m unittest discover -s exporter/tests -p 'test_*.py' -v` | Python shared-transport loader unit tests, outside the main discovery root. |
| `lake env lean MiriTests/Cast/Typed.lean` | Cast dispatcher, check order and size-mismatch cases; now included in `lake build MiriTests`. |
| `lake env lean --run MiriTests/Native/BytesOwnership.lean` | Included in `lake exe miri_tests`: host-byte ownership, release and copy-failure cleanup using fixture hosts. “Native” here names the boundary, not an execution mode. |
| `python3 tests/scheduling/test_source_prefix.py` | Extracted scheduler service prefix with fixture leaves, and `Stateful.lean` proof examples. |
| `MiriTests/FunctionPointers/*.lean` | Self-contained persistent reservation assertions are included in the runtime registry. |
| `tests/query_demand/make_cases.py` + `CatalogRoles.lean` | Generate mutations from fresh compiler evidence, then run readiness/obligation/provider assertions. Generator needs base/output paths, optional TLS base; run Lean `--run` with the generated directory. |

`exporter/tests/compare_shared_graph.py`, `compare_source126_compact.py` and
`check_runtime_type_closure.py` are additional argument-driven helpers. Read their
interfaces and supply matching inputs; merely placing them under `tests/` does
not schedule them.

## Choosing checks after a change

A green `check.sh` is useful broad regression evidence, but is insufficient if
related tests live outside its call graph. Select checks by the changed behavior,
not just the implementation filename. Shared decoder/memory/choice changes can
affect several rows below.

| Change | Checks to select in addition to broad regression coverage |
| --- | --- |
| Export schema, rustc query collection, roots or allocation identities | Exporter fixtures and transport tests; producer tests; input/frontend/runtime-metadata checks; fresh execution or fresh connected cases. Saved replay alone cannot test a changed exporter. |
| Decoder IDs, shared payloads or validation | Dedicated decoder suite, relevant input checks, transport tests, optimization parity if caches are involved; query-demand rejection cases where applicable. |
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
