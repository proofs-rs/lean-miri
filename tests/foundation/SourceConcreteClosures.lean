import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceConcreteTypes
import Miri.Input.SourcePhysical
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unavailable call type evidence accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected actual std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  IO.println s!"seed source present: {initial.canonical.sourceMaterial.isSome}"
  let mut world := initial
  for node in initial.canonical.instances do
    IO.println s!"demand {node.id}, source {world.canonical.sourceMaterial.isSome}"
    let (updated,_) ← checked ((SourceCompilerBodies.demandLoadedBody world node.id).mapError (fun e => s!"body {node.id}: {e}"))
    world := updated
  let some material := world.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := material.physical | throw (IO.userError "physical source absent")
  let mut nongeneric := 0
  for (expression,index) in physical.types.zipIdx do
    if let .closure source := expression then
      if source.parentCount == 0 then
        let concrete ← checked (SourceTypes.instantiate physical #[] #[] index)
        let (updated,_) ← checked (SourcePhysical.intern world concrete)
        world := updated
        nongeneric := nongeneric+1
  unless nongeneric > 0 do throw (IO.userError "genuine non-generic captured closure absent")
  let target ← checked (SourcePhysical.target world)
  let mut closures := 0
  for node in world.canonical.types do
    if let .closure _ _ _ := node.shape then
      let concrete ← checked (SourceConcreteTypes.concreteType world (target.pointerOffset.bytes.toNat*8) node.id)
      let (next,id) ← checked (SourcePhysical.intern world concrete)
      unless id == node.id && next.canonical.types.size == world.canonical.types.size do
        throw (IO.userError "closure inversion changed canonical identity or pool")
      closures := closures+1
      let .closure definition args count := node.shape | throw (IO.userError "closure shape changed")
      let badTypes := world.canonical.types.map fun row => if row.id == node.id then {row with shape := .closure definition args (count+1)} else row
      let bad := { world with canonical := { world.canonical with types := badTypes } }
      rejects (SourceConcreteTypes.concreteType bad (target.pointerOffset.bytes.toNat*8) node.id)
  unless closures > 0 do throw (IO.userError "no genuine closure demanded")
  rejects (SourceConcreteTypes.concreteType world (target.pointerOffset.bytes.toNat*8) world.canonical.types.size)
  IO.println "genuine closure complete arguments round-trip to exact canonical type; malformed count and missing type reject"
