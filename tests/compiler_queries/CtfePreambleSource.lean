import Miri.Input.CtfeMirSourceCodec
open Lean Miri.Input Miri.Interpreter.CompileTime
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path,typeName] := args | throw (IO.userError "source type")
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
  let programs ← must (sources.mapM CtfeMirSource.stackSource)
  let some selected := names.find? (·.2 == "callee") | throw (IO.userError "callee absent")
  let some argument := names.find? (·.2 == typeName) | throw (IO.userError "type absent")
  let rawRules ← must (json.getObjValAs? (Array Json) "rules")
  let rules ← must (rawRules.mapM fun value => do
    pure ({ declaration := ← value.getObjValAs? Nat "declaration"
            selfType := ← value.getObjValAs? Nat "self_type"
            valueDefinition := ← value.getObjValAs? Nat "value_definition" } : SourceStack.AssociatedSource))
  let resolve := SourceStack.sourceConstant programs rules ⟨64,false,true⟩ 100
  let (entered,machine) := SourceStack.push programs resolve selected.1.index #[.uint 32 9] #[argument.1.index] none {}
  match entered with
  | .error _ =>
    unless machine.steps == 0 && machine.counters == 0 && machine.requiredRequests.size == 1 &&
        machine.frames.head?.any (·.current.isNone) do throw (IO.userError "preamble failure initialized body")
    IO.println "preamble\terror\tpending\t1"
  | .ok () =>
    unless machine.requiredRequests.size == 2 do throw (IO.userError "ordered duplicate preamble omitted")
    IO.println "preamble\tok\t2"
    match SourceStack.run programs ⟨64,false,true⟩ resolve 1000 machine with
    | .returned (.uint _ value) machine =>
      for ((_,block,statement,counter),index) in machine.trace.zipIdx do
        IO.println s!"step\t{index}\t{block}\t{statement}\t{counter}"
      IO.println s!"result\t{machine.steps}\t{machine.counters}\t{value}"
    | _ => throw (IO.userError "unexpected preamble frame result")
