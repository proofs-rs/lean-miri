import Miri.Input.CtfeMirSourceCodec
open Lean Miri.Input Miri.Interpreter.CompileTime
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path,root,tiny,deny] := args | throw (IO.userError "source root tiny deny")
  let json ← must (Json.parse (← IO.FS.readFile path))
  let raw ← must (json.getObjValAs? (Array Json) "sources")
  let sources ← must (raw.mapM CtfeMirSourceCodec.read)
  let count ← must (json.getObjValAs? Nat "span_count")
  let definitions ← must (json.getObjValAs? (Array Json) "definitions")
  let names ← must (definitions.mapM fun value => do
    let definition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
    let name ← value.getObjValAs? String "name"
    pure (definition,name))
  must (CtfeMirSource.validateCatalogue count (fun definition => names.any (·.1 == definition)) sources)
  let programs ← must (sources.mapM fun source => do
    let program ← CtfeMirSource.stackSource source
    pure {program with name := (names.find? (·.1 == source.definition)).map (·.2) |>.getD ""})
  let some selected := programs.find? (·.name == root) | throw (IO.userError "root absent")
  let config : Counter.Config := ⟨64,tiny == "1",deny == "1"⟩
  let resolve := SourceStack.sourceConstant programs #[] config 100
  let (entered,machine) := SourceStack.push programs resolve selected.definition #[] #[] none {}
  must entered
  let output (machine : SourceStack.Machine) : IO Unit := do
    for ((definition,block,statement,counter),index) in machine.trace.zipIdx do
      let name := (programs.find? (·.definition == definition)).map (·.name) |>.getD "?"
      IO.println s!"step\t{index}\t{name}\t{block}\t{statement}\t{counter}"
  match SourceStack.run programs config resolve 1000000 machine with
  | .returned (.uint _ value) machine =>
    output machine
    IO.println s!"result\t{machine.steps}\t{machine.counters}\t{value}"
  | .failed error machine =>
    output machine
    IO.println s!"error\t{machine.steps}\t{machine.counters}\t{error}"
  | _ => throw (IO.userError "unexpected calls result")
