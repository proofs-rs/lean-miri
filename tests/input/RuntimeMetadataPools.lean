import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  for (node, index) in runtime.source.types.toList.zipIdx do
    let selected ← must ((runtime.node index).mapError toString)
    check (selected.id == index && selected.sourceLayout.normalizedType == node.sourceLayout.normalizedType &&
      selected.display == node.display) "type ID lookup changed its declaration"
    let concrete ← must ((runtime.lookup index).mapError toString)
    check (concrete.ty == node.sourceLayout.normalizedType) "layout calculation changed normalized type identity"
  check (!(runtime.node runtime.source.types.size).isOk) "out of bounds type accepted"
  let some first := runtime.source.types[0]? | throw (IO.userError "empty type pool")
  let invalidTypes := runtime.source.types.set! 0 { first with sourceLayout :=
    {first.sourceLayout with normalizedType := runtime.source.types.size} }
  let invalid : RuntimeMetadata := { source := { runtime.source with types := invalidTypes }, target := runtime.target }
  check (!(invalid.lookup 0).isOk) "out of bounds normalization accepted"
  let wrongTypes := runtime.source.types.set! 0 { first with id := 99 }
  let wrongIdentity : RuntimeMetadata := { source := { runtime.source with types := wrongTypes }, target := runtime.target }
  check (!(wrongIdentity.node 0).isOk) "type row/index mismatch accepted"
  IO.println s!"runtime typed declarations: {runtime.source.types.size} references and checked bounds passed"
