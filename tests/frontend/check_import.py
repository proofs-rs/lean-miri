"""Check that MIR reflection produces inspectable kernel declarations."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / "tools"))
from mir_json import load_mir_document

full, scoped = map(lambda p: str(Path(p).resolve()), sys.argv[1:])
scoped_type_count = len(load_mir_document(scoped)["types"])
with tempfile.TemporaryDirectory(prefix="lean-miri-reflection-") as directory:
    directory = Path(directory)
    source = directory / "Import.lean"
    source.write_text(f'''import Miri.Frontend.ImportMIR
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Miri.Frontend
namespace Client
import_mir {json.dumps(full)} as imported
example : imported.executionInput.isSome = false := by rfl
example : imported.document.producer.rustcCommit =
    "8144389c895da997dbdecaa635e41d6a50be6ffd" := by rfl
end Client
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``Client.imported) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "Imported value depends on an unapproved axiom: {{dependency}}"
def main : IO Unit := do
  let expected ← Miri.Input.decodeFile {json.dumps(full)}
  match expected with
  | .error message => throw (IO.userError message)
  | .ok expected =>
    unless expected.document.allocations.any (fun allocation =>
      match allocation.data with
      | some (.memory memory) => !memory.relocations.isEmpty
      | _ => false) do
      throw (IO.userError "reflection fixture has no compiler relocation evidence")
    unless Client.imported.document.raw == expected.document.raw do
      throw (IO.userError "raw JSON changed during reflection")
    unless Client.imported.document.sharedNodes == expected.document.sharedNodes do
      throw (IO.userError "shared JSON catalog changed during reflection")
    unless Client.imported.document.typedTree == expected.document.typedTree do
      throw (IO.userError "typed diagnostic tree changed during reflection")
    unless Client.imported.document.allocations.size == expected.document.allocations.size do
      throw (IO.userError "allocation count changed during reflection")
    for (actual, expected) in Client.imported.document.allocations.zip expected.document.allocations do
      match actual.data, expected.data with
      | some (.memory actual), some (.memory expected) =>
        unless actual.relocations.size == expected.relocations.size do
          throw (IO.userError "relocation count changed during reflection")
        for (actual, expected) in actual.relocations.zip expected.relocations do
          unless actual.ctfeProvenance == expected.ctfeProvenance do
            throw (IO.userError "CTFE provenance changed during reflection")
      | _, _ => pure ()
''')
    subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=root, check=True)
    source.write_text(f'''import Miri.Frontend.ImportMIR
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open Miri.Frontend
namespace Client
import_mir {json.dumps(scoped)} as selected
import_mir {json.dumps(scoped)} as selectedAgain
example : selected.document.bodies.size = 1 := by rfl
example : selected.document.types.size = {scoped_type_count} := by rfl
example : selected.executionInput.isSome = true := by rfl
example : selectedAgain.document.bodies.size = 1 := by rfl
example : selectedAgain.executionInput.isSome = true := by rfl
end Client
open Lean Elab Command in
run_cmd do
  for name in #[``Client.selected, ``Client.selectedAgain] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "Imported value depends on an unapproved axiom: {{dependency}}"
''')
    source.write_text(source.read_text() + '''
-- Runtime-only representation diagnostic; the imported declarations and their
-- kernel/axiom checks above remain safe. Pointer inspection is not a proof.
unsafe def main : IO Unit := do
  let value ← match Client.selected.document.raw.getObjVal? "types" with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let some node := Client.selected.document.sharedNodes.find? (· == value)
    | throw (IO.userError "sharing fixture has no catalog entry for types")
  unless ptrEq value node do
    throw (IO.userError "reflected raw JSON and catalog lost runtime sharing")
''')
    subprocess.run(["lake", "env", "lean", "--run", str(source)], cwd=root, check=True)
    print("MIR values reflected and kernel-checked; scoped readiness is not a safety theorem")
    invalid = directory / "invalid.json"
    invalid.write_text('{"schema_version":999}')
    source.write_text(f'''import Miri.Frontend.ImportMIR
open Miri.Frontend
import_mir {json.dumps(str(invalid))} as rejected
''')
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=root, text=True, capture_output=True)
    if result.returncode == 0 or "MIR import failed" not in result.stdout + result.stderr:
        raise SystemExit("malformed import did not fail closed")
    source.write_text('''import Miri.Frontend.ImportMIR
open Lean Elab Command in
run_cmd do
  let type := mkConst ``Nat
  let none := mkApp (mkConst ``Option.none [0]) type
  let proof := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (toExpr true)
  let value := mkApp3 (mkConst ``Miri.Frontend.checkedSome) type none proof
  liftCoreM <| addDecl <| .defnDecl {
    name := `forgedInput
    levelParams := []
    type := type
    value := value
    hints := .regular 0
    safety := .safe
  }
''')
    result = subprocess.run(["lake", "env", "lean", str(source)], cwd=root, text=True, capture_output=True)
    if result.returncode == 0 or "mismatch" not in result.stdout + result.stderr:
        raise SystemExit("kernel accepted a forged reflection success witness: " + result.stdout + result.stderr)
    print("malformed input and forged success witness rejected")
