import Miri.Input.Decoder

/-! rustc's array/slice field query returns the same element layout at every
index. The imported row at zero must exist and own that concrete layout. -/
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (value : Bool) (message : String) : IO Unit := do
  unless value do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh slice export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let mut checked := 0
  for node in document.types do
    if node.shapeKind == .slice || node.shapeKind == .array then
      let parent ← must ((runtime.lookup node.id).mapError toString)
      let expected ← must ((runtime.field parent 0).mapError toString)
      let (actual,_) ← must ((runtime.fieldLayoutForInWorld parent 777).run world.arena)
      check (actual == expected) s!"rustc element layout differs at index 777 for type {node.id}"
      let noProjection := {node with compilerFacts := (node.compilerFacts.map
        fun facts => {facts with projectionQueries := none})}
      let missingTypes := document.types.set! node.id noProjection
      let missingRuntime ← must ((RuntimeMetadata.ofDocument {document with types := missingTypes}).mapError toString)
      check (!((missingRuntime.fieldLayoutForInWorld parent 0).run world.arena).isOk)
        s!"missing rustc element projection was accepted for type {node.id}"
      checked := checked + 1
  check (checked >= 2) "fresh export lacked slice and array projection evidence"
  IO.println s!"PASS {checked} rustc array/slice field query families"
