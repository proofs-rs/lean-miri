import Miri.Input.LowerMIR
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.BodyIdentity

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: ProgramMIRIDs <export.json>")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJson source)
  let program ← must (lowerCoreProgram decoded.document)
  let input := decoded.document.mirTables
  unless program.bundle.bodies.size == input.bodies.size do
    throw (IO.userError "source body catalog differs from MIR tables")
  let mut places := 0
  for (id,index) in input.bodies.toList.zipIdx do
    let loaded ← must (Interpreter.LoadedBody.ofTables (.ofCanonicalIndex index) input.mir id)
    unless loaded.bodyId == id && loaded.identity.index == index do
      throw (IO.userError "loaded body lost canonical or wire identity")
    let some legacy := program.bundle.bodies[index]? | throw (IO.userError "body oracle absent")
    unless loaded.body.locals == legacy.body.locals && loaded.body.phase == legacy.body.phase &&
        loaded.body.argumentCount == legacy.body.argumentCount &&
        loaded.body.basicBlocks.size == legacy.body.basicBlocks.size do
      throw (IO.userError "body structural semantics changed")
    let some normalized := input.normalizedBodies[index]? | throw (IO.userError "normalization entry absent")
    match normalized with
    | .error _ => pure ()
    | .ok normalizedId =>
      let some types := input.normalization[index]? | throw (IO.userError "place type map absent")
      let types ← must types
      for (slot,placeId) in types.places.toList.zipIdx do
        if let some ty := slot then
          let place ← must (input.mir.places.lookup placeId)
          if normalizedId == id then
            unless place.typeId == ty do throw (IO.userError "identity normalization changed place type")
          unless ty < decoded.document.types.size do throw (IO.userError "normalized place type is out of bounds")
          places := places + 1
  IO.println s!"program MIR IDs: PASS ({input.bodies.size} canonical bodies; {places} body-scoped normalized place entries)"
