import Miri.Input.Decoder
import Miri.Input.SourceMir

/-! Fresh compiler source MIR creates tuple and ADT locals that the caller never
materializes. The returned execution universe must retain those exact types. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh novel-types source input")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let some index := document.bodies.findIdx? (fun seed => match seed with
    | .copyTemplate reference => match document.mirTemplates[reference.templateId]? with
      | some source => source.defPath.endsWith "local_types"
      | none => false
    | _ => false) | throw (IO.userError "local_types was not captured as a source template")
  let initial ← must (TypeArena.World.ofDocument document)
  let (body,world) ← must ((SourceMir.resolveBody document index).run initial)
  let some result := body.mir.locals[0]? | throw (IO.userError "return local is absent")
  let mut tuples := 0
  let mut adts := 0
  for id in body.mir.locals do
    if id < document.types.size then continue
    if (initial.lookupType id).isOk then throw (IO.userError "new local leaked into initial universe")
    match ← must (world.lookupType id) with
    | .constructed (.tuple fields) =>
      unless fields == #[result,result] do throw (IO.userError "new tuple lost its exact nominal children")
      tuples := tuples + 1
    | .constructed (.adt definition arguments) =>
      unless arguments == #[.Type result] do throw (IO.userError "new ADT lost its complete nominal arguments")
      let field ← must (GenericInstantiationWorld.instantiateFieldTerm world 1024 definition arguments 0 0)
      let (child,retained) ← must ((GenericInstantiationWorld.resolveType 1024 field).run world)
      unless child == result && retained.constructedTypes.size == world.constructedTypes.size do
        throw (IO.userError "raw ADT field substitution changed its nominal child identity")
      adts := adts + 1
    | _ => throw (IO.userError "unexpected novel local constructor")
  unless tuples > 0 && adts > 0 do throw (IO.userError "source fixture lacks absent tuple and ADT locals")
  let (again,retained) ← must ((SourceMir.resolveBody document index).run world)
  unless again.mir == body.mir && retained.constructedTypes.size == world.constructedTypes.size do
    throw (IO.userError "repeated body instantiation changed type identity or lost persistent state")
  IO.println s!"PASS fresh source MIR creates persistent absent tuple/ADT locals; tuples={tuples}; adts={adts}"
