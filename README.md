# lean-miri

A port of [Miri](https://github.com/rust-lang/miri), Rust's undefined-behavior
checker, to Lean 4. The goal is to prove that Rust programs are free of undefined
behavior under Miri's execution model.

Rust programs enter Lean as MIR and compiler metadata. A shared interpreter
executes that data and defines the semantics used in safety proofs.
The project is under development; the import and proof APIs are experimental.
See [STATUS.md](STATUS.md) for remaining work.

The exporter collects concrete function instances reachable from selected roots,
uses rustc to normalize their MIR and evaluate constants, and emits finite type
and declaration material. Lean computes layout, ABI, trait and vtable queries
from that material when needed. Lean execution does not call rustc and does not
instantiate generic function MIR. JSON is decoded into typed input once;
execution state and caches belong to the individual run.

## API reference

Browse the [Miri API reference](https://proofs-rs.github.io/lean-miri/Miri.html),
generated with doc-gen4 from `main`. The import and proof APIs remain experimental.
See [Building the API reference](docs/development.md#building-the-api-reference)
for local generation and hosting details.

## Build

With [Elan](https://github.com/leanprover/elan) installed, run:

```bash
lake build
```

Lake uses the Lean version in `lean-toolchain` and builds the library and all
self-contained `MiriTests` modules. Use `lake build Miri` for the library alone. Building native executables also requires a C compiler.
Rust is needed only for exporting new Rust inputs and upstream comparison tests.

Alternatively, install Lean locally with `bash tools/setup-lean.sh`, then use
`ELAN_HOME="$PWD/.elan" .elan/bin/lake build`.

## Usage

### Run a Rust program

The execution pipeline is Rust source → exported MIR JSON → Lean interpreter.
From the repository root, `lake run interpret` builds the pinned Rust compiler,
the MIR exporter, the Miri sysroot, and the native Lean runner, then exports
and executes one Rust source. `rustup` and `cargo` must already be available.
On Linux x86_64:

```bash
mkdir -p scratch
cat > scratch/example.rs <<'RS'
fn main() {
    assert_eq!(std::hint::black_box(1_u32) + 1, 2);
}
RS
lake run interpret -- scratch/example.rs
```

The JSON is written to `scratch/example.json`. An executable's entry function
is selected. Repeat `--root DEF-PATH` to select exact functions, and put rustc
arguments after `--`. `lake build rustToolchain`, `lake build exporter`, and
`lake build miriReference` build those pieces alone; a bare `lake build` does
not. `tools/setup-miri-reference.sh`, `tools/build-exporter.sh`,
`tools/export-mir.sh`, and `tools/run.sh` call the Lake scripts of the same
names through `lake` on `PATH`. `build-exporter.sh --features miri-reference`
builds the separate `exporterMiriReference` target under
`scratch/lake/exporter-miri-reference`. `export-mir.sh` rebuilds the ordinary
exporter before each export; it does not build the Miri sysroot. Setup is
described in the
[Rust setup instructions](docs/development.md#rust-toolchain-and-reference-setup).

Inspect the final `run:` line: `finalized_exit code=0` reports normal completion;
`undefined_behavior`, `unsupported`, `failed` and `pending` report other outcomes.
The runner can exit with status zero even when the guest does not complete, so
its process exit code alone is insufficient. Proving safety requires a Lean
theorem covering all permitted executions.

### Work with the input in Lean

To inspect a single function, export the included `add_one` example with `--root`.
This avoids importing the full standard-library startup graph into Lean:

```bash
lake run interpret -- exporter/fixtures/scope/simple.rs \
  --no-run --output scratch/add-one.json --root add_one \
  --crate-name scoped_closure -- --crate-type=lib
```

Create `scratch/Example.lean`:

```lean
import Miri.Frontend.ImportMIR

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

open Miri.Frontend
import_mir "scratch/add-one.json" as program

#check program.document
#check program
```

Check it with `lake build Miri.Frontend.ImportMIR`, then
`lake env lean scratch/Example.lean`. The options increase the elaboration budget
for reflecting the input. `import_mir` turns the exported data into Lean constants;
it does not generate a safety proof.
[OperationalSafety](Miri/OperationalSafety.lean) defines safety, and
[its examples](MiriTests/Safety/OperationalSafety.lean) demonstrate the proof interface.
See the [exporter guide](exporter/README.md) for selecting functions with `--root`,
exporting Cargo projects and the input format.
An executable defaults to its entry function; libraries require explicit roots.
Repeated `--root` options select multiple functions. A selected generic function
contributes a declaration; only discovered concrete instances have executable
MIR. Schema 14 requires fresh exports from earlier input formats.

### Generate verification conditions for interpreter steps

Import `Miri.Verification.ExactWP` and enable `set_option experimental.vcgen true`.
Use `vcgen` on a `Std.WP.Triple` for `Miri.Verification.StepWP.OutcomeStep.step`.
The success postcondition can inspect the driver flag and successor state.
The error postcondition receives the error and the state where execution stopped.
The generated precondition covers every permitted choice. Use
`simp only [miri_rvalue]` with the selected MIR and frame facts to expose the
canonical assignment's place, operand, and copy effects. See the
[assignment proof fixture](MiriTests/Verification/RvalueWP.lean).

After selecting a MIR instruction in the generated VC, use
`miri_instruction_wp` to open its rule for `SetDiscriminant`, `StorageLive`,
`PlaceMention`, statement intrinsics, `Drop`, `Assert` or `UnwindTerminate`. Each rule keeps the
state at which an error occurs. For example, `miri_drop_wp` further exposes
the empty-glue jump and the dispatch request for a destructor.
For managed fresh stack storage, `miri_storage_live` also exposes the
reserved allocation ID, root tag, address draw, aligned base address and
publication in the address maps. See the [Drop step fixture](MiriTests/Verification/DropWP.lean)
and the [storage activation examples](MiriTests/Verification/StorageLiveWP.lean).

For a ranged Tree Borrows read followed by a write, `miri_tree_range_wp`
pulls both continuations through the prepared segments in order. A read
failure skips the write. A write failure passes its own trace and the
partially updated tree to the error postcondition. With errors rejected,
`miri_tree_range_wp snapshots` exposes each initial segment's permission
checks and retained result. A lookup in the resulting map uses its last
matching cursor, with the untouched location as the fallback.
For a safety goal with success `True` and error `False`, use
`miri_tree_range_wp safety` on the WP or the nested precondition produced by
`vcgen`. It obtains each retained read location from its contract. Use
`miri_tree_range_wp pointwise` to supply local read results explicitly.
Write preparation sees the pointwise read
results, including any split or merge at the new byte boundaries. For a
full, uniform, single-root range, the normal-access theorem reduces safety
to the initial per-node permission and protector checks under its stated
topology and cache hypotheses. See the [pointwise range examples](MiriTests/Verification/TreeRangePointwiseWP.lean),
[normal read/write examples](MiriTests/Verification/TreeVisitWP.lean)
and [partial-failure examples](MiriTests/Verification/TreeRangeOutcomeWP.lean).

For a well-formed location map and in-bounds read and write ranges, the
`miri_tree_range_wp bytes` separates read-only, write-only and intersecting bytes. Only an
intersecting byte needs the read's permission and cache changes when the
write is checked. Wildcard access exposes each root's exposure counters,
permissions, protectors and child checks. See the
[byte-range examples](MiriTests/Verification/TreeOverlapWP.lean) and
[wildcard forest examples](MiriTests/Verification/TreeWildcardPairWP.lean).

Use `miri_copy_tree_wp` on the selected copy statement. Its concrete rule
checks the source access before loading the destination
for writing. A same-allocation destination can therefore observe the borrow
state committed by the read. Use `miri_copy_bytes_wp` to inspect the
physical copy stages, including initialization and provenance updates.
The checked operands from the exported
`duplicate_prefix` helper are used in the
[copy statement proof](examples/duplicate_prefix_vcgen/CopyStatementTreeVC.lean).

For a canonical call, use `miri_call_dispatch_wp` on the call precondition
produced by `vcgen`. It opens one dispatch iteration and its ABI, pointer,
virtual, intrinsic or foreign-call checks. Apply it again when a fallback
produces another request. The [dispatch examples](MiriTests/Verification/CallDispatchWP.lean)
show how to reduce the error branch to a predicate on the retained state.

Build the Goto/Nop, Call/Return, dispatch and protected-alias proof fixtures.

```bash
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  MiriTests.Verification.StepWP MiriTests.Verification.CallReturnWP \
  MiriTests.Verification.CallDispatchWP MiriTests.Verification.TreeBorrowsWP
```

### Generate a whole-body verification condition

With the pinned Rust and Lean tools set up, generate and check a safety VC from
a Rust source file or an exported MIR JSON document.

```bash
tools/body-vc safety examples/body_vcgen/control.rs \
  --output scratch/ControlSafety.lean
```

The command saves the Lean condition and the paired MIR JSON. It reports
generation time and the time to check that the generated file is well typed.
Rust source exports use the pinned MIR-enabled sysroot and `-Cpanic=abort`.
The generated file specializes each known transfer against its imported MIR
instruction using exact WP rewrites. In Lean, use `#print` on a declaration
such as `GeneratedBodySafety.transfer_0_bb0_0` to inspect its `pre` field.
It takes the driver choice, success and error continuations, and machine
state. Locations with identical instructions share a transfer. Branches,
loops and calls use the shared whole-body condition for their successors.
States outside the imported graph use the interpreter's canonical rule.

`safetySpec` characterizes the VC at a prepared entry. It holds exactly
when the frame matches the imported entry and every permitted finite error
in the call scope is classified as non-UB. The exact rewrite `requiredAt_eq`
connects the generated condition to proofs over the canonical VC. To see a
proof that supplies these facts for a concrete Rust function and its admitted
caller domain, follow the [empty_function example](examples/empty_function/README.md#generated-body-verification-condition).

For a direct Lean `vcgen` proof, use this operation in a `Triple` with your
precondition and success and error postconditions.

```lean
GeneratedBodySafety.run config limits program allowed
```

Enable `set_option experimental.vcgen true`. After `vcgen`, unfold
`GeneratedBodySafety.entryPre` to expose the compiler-selected entry window.
Each `window_<body>_bb<block>_<slot>` composes the transfers through the rest
of that basic block. The continuation sees the actual successor state,
including the state used to check the next permitted choice. Use
`GeneratedBodyVC.windowPre_at` when you have a proof of the next selected row.
If the successor leaves the window, the VC uses the shared whole-body
continuation. A matched call terminator opens the actual callee scope and
resumes the caller from the state left by the callee. Use
`GeneratedBodyVC.windowPre_call` to select that summary at a known row,
or `GeneratedBodyVC.sharedPre_iff_call` at a live call boundary in the
shared continuation.

After selecting a window row, unfold its emitted transfer to expose its
effects. `miri_copy_initial_wp` applies the checked copy and successor-load
rewrites when the necessary range and provenance facts are in scope.
The `miri_initial_wp` simp set also exposes typed pointer formation and
the associated Tree Borrows checks.

Use `miri_generated_program` for the single-row view of
`GeneratedBodyVC.run`. Use `miri_generated_window` with an emitted window name
to substitute that window into a generated control precondition.

To check an observation partway through a block, take the relevant prefix of
the emitted window and use `GeneratedBodyVC.windowPrefixPre` with a
postcondition on the state at its last step. This condition checks each
selected instruction and passes an error and its retained state directly to
the error postcondition. The copy and pointer examples connect this exact
prefix condition to executable checks on exported MIR.
[Copy and pointer examples](examples/pointer_observation_vcgen)

Export the Rust function and import the execution input with
`Miri.Frontend.ImportMIR`. In a Lean client, import
`Miri.Verification.BodyVCGen` and enable `set_option experimental.vcgen true`.
Select a non-generic exported root with `BodyVCGen.loadProgram input rootIndex`.
To include the known imported callees, use `vcgen` on a `Std.WP.Triple` for
`BodyVCGen.runProgram config limits program allowed`. For a supplied MIR
`Body`, use `BodyVCGen.run config limits body allowed`. Give the triple a
predicate on the prepared entry state, a success postcondition, and an error
postcondition. The `allowed` predicate specifies the admitted driver choices.

The generated condition checks the prepared frame at its entry PC. It uses a
shared equation at each compiled MIR location and follows the state left by
the driver through branches, loops, and calls, including same-depth frame
replacement. The success continuation receives either `.scopeExit` or
`.stopped`. The error continuation receives the typed error and exact failed
state. The weakest liberal precondition covers every permitted finite outcome,
including errors reached after arbitrarily many loop iterations. Divergence and
states with no permitted choices have no outcome to check.

Use `miri_program` or `miri_body` after `vcgen` to reveal one symbolic
transfer. A successor with decreasing graph rank uses substitution. Other
successors refer to a shared condition. `BodyVCGen.generateProgram` exposes
the graph and generated obligations indexed by loaded body identity.
`BodyVCGen.ProgramNoUB` accepts success and the interpreter's non-UB error
outcomes, including cutoffs. See the [imported Rust example](examples/body_vcgen/README.md).

Generation needs no block triples, loop invariants, or callee contracts.
Proving the resulting condition may still require an invariant for an
unbounded loop, an admissibility argument for the choice policy, or facts about
the initial machine state. The interpreter configuration supplies resource
limits and models the effects on the actual driver path. Use
`Miri.Verification.CheckedBodyVCGen` for choice-specific core configurations
that can fail before the first inner transition. Its outcomes include errors
from configuration selection and the resulting outer state. The enclosing
executable loop owns outer scheduling and stack-empty callbacks.
The [imported MIR example](examples/body_vcgen/Verify.lean) generates conditions
for a Rust function containing a branch, a loop, and a call.

```bash
flock --no-fork /tmp/lean-miri-lake-build.lock lake build \
  Miri.Verification.BodyVCGen Miri.Frontend.ImportMIR \
  MiriTests.Verification.WholeBodyWP MiriTests.Verification.WholeBodyReplay
lake env lean examples/body_vcgen/Verify.lean
lake env lean examples/body_vcgen/Replay.lean
```

Measure generation and type checking for growing synthetic CFGs and the same
imported input. The benchmark writes its results under `scratch/`.

```bash
python3 tools/measure-whole-body.py --output scratch/whole-body-bench \
  --import-json examples/body_vcgen/input.json
```

## Tests

Run `lake build MiriTests` for self-contained Lean test modules, then
`lake exe miri_tests` to execute the registered assertions (including cached
`#eval` cases). Use `lake exe miri_tests --list` or `--case MODULE` to select a case.
External comparisons and input-driven checks remain under `tests/`.

`lake build` checks Lean definitions and proofs in the default targets.
Additional tests check that the port behaves like the pinned Miri implementation,
and that the exporter and input decoder agree. Compilation alone does not check
that correspondence.

See the [test guide](tests/README.md) for the suite layout, check inclusion,
standalone tests and checks to select after a change. The
[development guide](docs/development.md#what-the-checks-test) covers setup and
validation commands.

## Layout

| Location | Contents |
| --- | --- |
| [Miri/](Miri/) | Lean interpreter, semantics and theorems |
| [exporter/](exporter/README.md) | Rust compiler frontend that produces MIR JSON |
| [MiriTests/](MiriTests/) | Self-contained Lean proofs and executable assertions |
| [tests/](tests/) | Component tests, integration tests, proof examples and fixtures |
| [tools/](tools/) | Setup, execution, validation and source audit tools |
| [upstream/](upstream/) | Reference source snapshots; revisions and hashes are in [upstream/source-lock.json](upstream/source-lock.json) |
| [native/](native/) | C support for native math calls |
| [third_party/](third_party/) | External source data and license notices |

The [development guide](docs/development.md#source-audit-tools) explains the audit
tools and current directory conventions. For runtime measurements, see the
[profiling guide](tools/PROFILING.md).

## Authors and credits

See [AUTHORS](AUTHORS) for authors of the Lean port and project code.
Miri's original implementation and design are by the
[Miri developers and contributors](https://github.com/rust-lang/miri).
See [THIRD_PARTY.md](THIRD_PARTY.md) for upstream attribution and licenses.
