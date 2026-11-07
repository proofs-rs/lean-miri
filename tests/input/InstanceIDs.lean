import Miri.Input.CompilerInstance
import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: InstanceIDs <export.json>")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJson source)
  let document := decoded.document
  let context := LowerContext.ofDocument document
  let input := document.mirTables
  unless input.instances.size == document.instances.size do throw (IO.userError "instance table length changed")
  let mut available := 0
  let mut unavailable := 0
  for row in document.instances do
    let expected := CompilerInstance.decode context input.compiler row.payload
    let actual := input.instance row.id
    match expected,actual with
    | .ok (value,tables), .ok cached =>
      unless value == cached do throw (IO.userError s!"instance {row.id} semantic value changed: expected={repr value}; actual={repr cached}")
      unless tables.definitions == input.compiler.definitions && tables.typeConstants == input.compiler.typeConstants do
        throw (IO.userError s!"instance {row.id} was not constructed at input time")
      available := available + 1
    | .error _, .error _ => unavailable := unavailable + 1
    | .ok _, .error reason => throw (IO.userError s!"instance {row.id} rejected: {reason}")
    | .error reason, .ok _ => throw (IO.userError s!"instance {row.id} accepted beyond independent decoder: {reason}")
  unless !(input.instance input.instances.size).isOk do throw (IO.userError "out-of-bounds instance accepted")
  IO.println s!"instance IDs: PASS ({available} semantic values; {unavailable} unavailable; fixed table and bounds)"
