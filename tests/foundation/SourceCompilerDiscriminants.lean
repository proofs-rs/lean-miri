import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerDiscriminants
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unsupported discriminant query accepted") | .error _ => pure ()

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let runtime ← checked ((Input.RuntimeMetadata.ofDocument world.canonical).mapError toString)
  let expected ← checked (Input.CompilerPrimitiveFacts.primitiveLayout runtime "u8")
  let mut sawClosure := false
  let mut checkedKinds : Array Input.TypeShapeKind := #[]
  for node in world.canonical.types do
    match node.shape with
    | .closure .. | .functionPointer .. | .reference .. | .dynamicTraitObject .. | .tuple _ =>
      let layout ← checked (Input.SourceCompilerDiscriminants.layout runtime node.id)
      unless layout == expected do throw (IO.userError "source nonenum discriminant type differs from canonical u8")
      -- rustc returns None for any requested index on a type without variants;
      -- the fixed interpreter separately enforces index zero when appropriate.
      for variant in [0,17] do
        unless (← checked (Input.SourceCompilerDiscriminants.value runtime node.id variant)).isNone do
          throw (IO.userError "source nonenum acquired an invented declared discriminant")
      if node.shapeKind == .closure then
        sawClosure := true
        rejects (Input.SourceCompilerDiscriminants.variantCount runtime node.id)
      checkedKinds := checkedKinds.push node.shapeKind
    | _ => pure ()
  unless sawClosure && checkedKinds.contains .reference && checkedKinds.contains .dynamicTraitObject &&
      checkedKinds.contains .functionPointer && checkedKinds.contains .tuple do
    throw (IO.userError "genuine nonenum constructor domain not exercised")
  rejects (Input.SourceCompilerDiscriminants.layout runtime world.canonical.types.size)
  IO.println "current source nonenum discriminant types/None values pass across closure, function pointer, references, dyn and tuples without compiler-facts rows"
