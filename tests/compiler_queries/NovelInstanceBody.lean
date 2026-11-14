import Miri.Input.Decoder
import Miri.Input.CallResolution

/-! A complete instance key outside the imported rustc prefix has no body
result, even when its syntax matches a known compiler instance. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh instance fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let some oracle := document.instances[4]? | throw (IO.userError "concrete instance oracle absent")
  let store ← must (InstanceArena.Store.ofSource initial.arena (document.instances.extract 0 3))
  let world := {initial with instances := store, bodies := BodyArena.Store.ofSource #[]}
  let (id,world) ← must ((RuntimeArrayTypes.internInstance oracle.instanceKind oracle.genericArgs).run world)
  unless id == 3 do throw (IO.userError "novel instance did not append after material prefix")
  let prepared ← must (CallResolution.prepareWithRuntime metadata (← must (lowerProgram document)))
  match (CallResolution.loadedBodyOfInstance prepared id).run world with
  | .error "constructed instance has no exact rustc body result" => pure ()
  | .error error => throw (IO.userError s!"unexpected constructed body error: {error}")
  | .ok _ => throw (IO.userError "constructed instance borrowed rustc body")
  IO.println "PASS constructed instance body requires exact rustc result"
