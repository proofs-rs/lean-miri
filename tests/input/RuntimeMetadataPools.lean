import MiriTests.Input.LegacyFixture
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter input")
  let decoded ← must (decodeFixture (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  for (node, index) in runtime.source.types.toList.zipIdx do
    let selected ← must ((runtime.node index).mapError toString)
    check (selected.id == index && selected.layoutId == node.layoutId && selected.display == node.display) "type ID lookup changed its definition"
    let some layout := runtime.source.layouts[node.layoutId]? | throw (IO.userError "missing layout definition")
    check (decide (runtime.lookup index = (do
      let physical ← RuntimeMetadata.layout runtime.target layout
      pure ⟨index, physical⟩))) "type layout ID resolved to the wrong physical definition"
  -- IDs beyond the material table now denote lazy constructor recipes.
  let constructed ← must ((runtime.node runtime.source.types.size).mapError toString)
  check (match constructed.shape with | .rawPointer 0 .Mut => true | _ => false)
    "first lazy type ID does not reconstruct its exact pointer recipe"
  check (!(runtime.layoutById runtime.source.layouts.size).isOk) "out of bounds layout accepted"
  let some first := runtime.source.types[0]? | throw (IO.userError "empty type pool")
  let invalidTypes := runtime.source.types.set! 0 { first with layoutId := runtime.source.layouts.size }
  let invalid := { runtime with source := { runtime.source with types := invalidTypes }, denseTypes := none }
  check (!(invalid.lookup 0).isOk) "out of bounds layout hidden by previous metadata preparation"
  let wrongTypes := runtime.source.types.set! 0 { first with id := 99 }
  let wrongIdentity := { runtime with source := { runtime.source with types := wrongTypes }, denseTypes := none }
  check (!(wrongIdentity.node 0).isOk) "type row/index mismatch accepted"
  IO.println s!"runtime typed pools: {runtime.source.types.size} type references; direct physical layouts and checked bounds passed"
