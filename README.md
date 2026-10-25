# lean-miri

A port of [Miri](https://github.com/rust-lang/miri), Rust's undefined-behavior
checker, to Lean 4. The goal is to prove that Rust programs are free of undefined
behavior under Miri's execution model.

Rust programs enter Lean as MIR and compiler metadata. A shared interpreter
executes that data and defines the semantics used in safety proofs.
The project is under development; the import and proof APIs are experimental.
See [STATUS.md](STATUS.md) for remaining work.

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
On Linux x86_64, first prepare the pinned Rust compiler and MIR-enabled standard
library using the [Rust setup instructions](docs/development.md#rust-toolchain-and-reference-setup).
Then, from the repository root:

```bash
bash tools/build-exporter.sh
mkdir -p scratch
cat > scratch/example.rs <<'RS'
fn main() {
    assert_eq!(std::hint::black_box(1_u32) + 1, 2);
}
RS
LEAN_MIRI_PREPARED_ALLOC_ID_WORLD=1 bash tools/export-mir.sh \
  --output scratch/example.json -- scratch/example.rs --crate-name example
bash tools/run.sh scratch/example.json
```

The last command builds and caches the native Lean runner, then executes the
exported input. Build logs are saved under `scratch/`. Inspect the final `run:`
line: `finalized_exit code=0` reports normal completion; `undefined_behavior`,
`unsupported`, `failed` and `pending` report other outcomes. The runner can exit
with status zero even when the guest does not complete, so its process exit code
alone is insufficient. Proving safety requires a Lean theorem covering all
permitted executions.

### Work with the input in Lean

To inspect a single function, export the included `add_one` example with `--root`.
This avoids importing the full standard-library startup graph into Lean:

```bash
bash tools/export-mir.sh --output scratch/add-one.json --root add_one -- \
  exporter/fixtures/scope/simple.rs --crate-type=lib --crate-name=scoped_closure
```

Create `scratch/Example.lean`:

```lean
import Miri.Frontend.ImportMIR

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

open Miri.Frontend
import_mir "scratch/add-one.json" as program

#check program.document
#check program.executionInput
```

Check it with `lake build Miri.Frontend.ImportMIR`, then
`lake env lean scratch/Example.lean`. The options increase the elaboration budget
for reflecting the input. `import_mir` turns the exported data into Lean constants;
it does not generate a safety proof.
[OperationalSafety](Miri/OperationalSafety.lean) defines safety, and
[its examples](MiriTests/Safety/OperationalSafety.lean) demonstrate the proof interface.
See the [exporter guide](exporter/README.md) for selecting functions with `--root`,
exporting Cargo projects and the input format.

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
