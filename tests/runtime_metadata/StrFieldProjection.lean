import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input Miri.ABI

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def fields (runtime : RuntimeMetadata) (strId byteId : Nat) : IO Unit := do
  let parent ← must (runtime.lookup strId)
  let expected ← must (runtime.lookup byteId)
  for index in [0, 1, 7, 99, 123456789] do
    let actual ← must (runtime.field parent index)
    unless actual == expected do throw (IO.userError s!"str field {index} differs from canonical u8")

def main (args : List String) : IO Unit := do
  let path := args.head?.getD "examples/empty_function/input.json"
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let some str := runtime.source.types.find? (·.shapeKind == .str)
    | throw (IO.userError "fixture lacks str")
  let some byte := runtime.source.types.find? (fun node =>
      node.shapeKind == .uint && node.shapeMetadata.unsignedKind == some (.known .u8))
    | throw (IO.userError "fixture lacks u8")
  fields runtime str.id byte.id
  let types := runtime.source.types.map fun node =>
    if node.id == str.id then {node with compilerFacts := node.compilerFacts.map fun facts => {facts with projectionQuery := none}}
    else node
  let queryFree := {runtime with source := {runtime.source with types}}
  fields queryFree str.id byte.id
  let absent := {queryFree with source := {queryFree.source with types := types.map fun node =>
    if node.id == byte.id then {node with shapeStatus := .unsupported} else node}}
  let parent ← must (absent.lookup str.id)
  unless !(absent.field parent 7).isOk do throw (IO.userError "str field accepted missing canonical u8")
  let duplicate := {byte with id := types.size}
  let ambiguous := {queryFree with source := {queryFree.source with types := types.push duplicate}}
  let parent ← must (ambiguous.lookup str.id)
  unless !(ambiguous.field parent 7).isOk do throw (IO.userError "str field accepted ambiguous canonical u8")
  IO.println "str field projection: PASS (explicit query, query-free branch, absent/ambiguous u8)"
