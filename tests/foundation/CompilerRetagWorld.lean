import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.CompilerRetagWorld
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unavailable source retag query accepted") | .error _ => pure ()

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let mut references := 0
  let mut raw := 0
  let mut closures := 0
  let mut functions := 0
  for node in world.canonical.types do
    let shape ← checked (Input.CompilerRetagWorld.typeShape world node.id)
    match node.shape with
    | .reference pointee mutable _ =>
      references := references + 1
      unless shape.classify == .reference &&
          (← checked (Input.CompilerRetagWorld.referencePointee world node.id)) == (pointee,mutable) &&
          (← checked (Input.CompilerRetagWorld.builtinDeref world node.id)) == pointee do
        throw (IO.userError "current source reference shape/pointee differs")
    | .rawPointer pointee _ =>
      raw := raw + 1
      unless shape.classify == .rawPointer &&
          (← checked (Input.CompilerRetagWorld.builtinDeref world node.id)) == pointee do
        throw (IO.userError "current source raw pointer shape/deref differs")
    | .functionPointer .. =>
      functions := functions + 1
      unless shape.classify == .invalidType &&
          (← checked (Input.SourceCompilerAutoTraits.check world .unpin node.id)) do
        throw (IO.userError "function pointer fast path/retag shape differs")
      rejects (Input.CompilerRetagWorld.referencePointee world node.id)
    | .closure _ args _ =>
      closures := closures + 1
      unless shape.classify == .invalidType do throw (IO.userError "closure acquired an invented pointer/Box role")
      -- A captured function pointer proves the tuple fast path, but the closure
      -- root itself requires the separately supplied auto-trait source solver.
      let some (.Type tuple) := args.back? | throw (IO.userError "closure tuple absent")
      unless (← checked (Input.SourceCompilerAutoTraits.check world .unpin tuple)) do throw (IO.userError "upvar tuple fast path differs")
      for role in #[Input.SourceAbi.AutoTraitRole.unpin, .unsafeUnpin, .freeze] do
        unless (← checked (Input.SourceCompilerAutoTraits.check world role node.id)) do
          throw (IO.userError "genuine closure auto-trait proof differs")
      let unavailable := {world with canonical := {world.canonical with sourceMaterial := none}}
      rejects (Input.SourceCompilerAutoTraits.check unavailable .unpin node.id)
    | _ => pure ()
  unless references > 0 && raw > 0 && closures > 0 && functions > 0 do throw (IO.userError "source constructor domain absent")
  rejects (Input.CompilerRetagWorld.typeShape world world.canonical.types.size)
  IO.println "current source retag shapes/pointees and checked closure auto traits pass; missing evidence rejects"
