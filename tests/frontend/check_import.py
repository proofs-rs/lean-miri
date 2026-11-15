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
example : imported.document.producer.rustcCommit =
    "8144389c895da997dbdecaa635e41d6a50be6ffd" := by rfl
end Client
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``Client.imported) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "Imported value depends on an unapproved axiom: {{dependency}}"
def classicTables (d : Miri.Input.ImportDocument) :=
  (d.compilerPredicates, d.compilerAbiLayoutSchema, d.producer, d.runtimeTargetDataLayout, d.predicates, d.definitions, d.typeConstants, d.layouts, d.files, d.spans, d.types, d.allocations, d.compilerAllocIdWorld, d.instances, d.selectedScope, d.functionAbis, d.bodyRoots, d.bodies, d.coroutineCoverage, d.queries, d.producerSettings)
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
    unless Client.imported.document.sourceMaterial.isNone && expected.document.sourceMaterial.isNone do
      throw (IO.userError "classic reflection unexpectedly acquired generic source")
    unless Lean.toExpr (classicTables Client.imported.document) == Lean.toExpr (classicTables expected.document) do
      throw (IO.userError "typed compiler tables changed during reflection")
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
example : selected.document.bodyRoots.size = 1 := by rfl
example : selected.document.types.size = {scoped_type_count} := by rfl
example : selectedAgain.document.bodyRoots.size = 1 := by rfl
end Client
open Lean Elab Command in
run_cmd do
  for name in #[``Client.selected, ``Client.selectedAgain] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "Imported value depends on an unapproved axiom: {{dependency}}"
''')
    subprocess.run(["lake", "env", "lean", str(source)], cwd=root, check=True)
    print("MIR values reflected and kernel-checked; accepted input is not a safety theorem")
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
    source.write_text(f'''import Miri.Frontend.ImportMIR
open Lean Elab Command in
run_cmd do
  let decoded ← liftIO <| Miri.Input.decodeFile {json.dumps(scoped)}
  let input ← match decoded with
    | .ok value => pure value
    | .error error => throwError "{{error}}"
  -- Deliberately invalid source payload: presence alone must be rejected.
  let material : Miri.Input.SourceMaterial := {{
    target := {{ triple := "", architecture := "", dataLayout := "", pointerSizeBits := 0, endian := "" }}
    declarations := #[], genericLayers := #[] }}
  let input := {{ input with document := {{ input.document with sourceMaterial := some material }} }}
  let rejected ← liftTermElabM do
    try
      let _ ← Miri.Frontend.quoteSchema12Input input
      pure false
    catch _ => pure true
  unless rejected do throwError "generic source material was silently quoted as schema12"
''')
    subprocess.run(["lake", "env", "lean", str(source)], cwd=root, check=True)
    print("malformed input and forged success witness rejected")
