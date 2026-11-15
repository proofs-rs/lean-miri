import Miri.Frontend.FoundationInput
import Miri.Input.EvalPreparation
import Miri.Interpreter.GlobalConstructors
open Lean Miri Miri.Interpreter Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std foundation source")
  let decoded ← checked (decodeRunnerInputProfiled (← IO.FS.readFile path) {})
  let program ← checked (Input.lowerProgram decoded.document)
  let prepared ← checked (Input.EvalPreparation.prepareProfiled {} program).outcome
  let queries ← checked prepared.compiler.main.sections
  unless queries.size == 1 do throw (IO.userError "genuine std selected declaration count changed")
  let some entry := queries[0]? | throw (IO.userError "source section disappeared")
  unless entry.name == ".init_array.00099" do throw (IO.userError "source section name changed")
  unless !(constructorSectionMatches .elf entry.name) do
    throw (IO.userError "fixed ELF constructor predicate changed")
  unless (queries.filter (fun row => constructorSectionMatches .elf row.name)).isEmpty do
    throw (IO.userError "ELF constructor declaration traversal was not empty")
  match entry.result with
  | .error error => unless error.startsWith "source link-section initializer/allocation capability unavailable" do
      throw (IO.userError error)
  | .ok _ => throw (IO.userError "source declaration fabricated an initializer allocation")
  let some material := decoded.document.sourceMaterial
    | throw (IO.userError "typed source material absent")
  let missing ← checked (Input.lowerProgram {decoded.document with
    sourceMaterial := some {material with linkSections := none}})
  let missingPrepared ← checked (Input.EvalPreparation.prepareProfiled {} missing).outcome
  match missingPrepared.compiler.main.sections with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unknown source section coverage became a known empty query")
  IO.println "source sections: genuine nonempty std declaration retained; exact fixed ELF predicate excludes it; initializer demand remains Unsupported"
