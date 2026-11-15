import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceFunctionTypes
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "missing nested FnDef header accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: complete finite nested FnDef headers")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := source.physical | throw (IO.userError "types absent")
  let some abi := source.abi | throw (IO.userError "headers absent")
  let mut count := 0
  for (expression,reference) in physical.types.zipIdx do
    if let .functionDefinition _ arguments := expression then
      for (argument,slot) in arguments.zipIdx do
        if let .type child := argument then
          if let some (.functionDefinition definition _) := physical.types[child]? then
            let some declared := physical.definitions[definition]? | throw (IO.userError "child definition absent")
            let (world,id) ← checked (SourceFunctionTypes.internSource initial reference #[] #[])
            let some outer := world.canonical.types[id]? | throw (IO.userError "outer type absent")
            let .functionDefinition _ args signature _ := outer.shape | throw (IO.userError "outer FnDef identity lost")
            let some (.Type childId) := args[slot]? | throw (IO.userError "nested canonical generic argument absent")
            let some childNode := world.canonical.types[childId]? | throw (IO.userError "child type absent")
            let .functionDefinition .. := childNode.shape | throw (IO.userError "function item was erased to function pointer")
            unless signature.inputs.contains childId do throw (IO.userError "signature generic binding did not retain function item")
            let (same,again) ← checked (SourceFunctionTypes.internSource world reference #[] #[])
            unless again == id && same.canonical.types.size == world.canonical.types.size do
              throw (IO.userError "nested FnDef demand is not canonical")
            let missing := {source with abi := some {abi with functions := abi.functions.filter (·.definition != declared.raw)}}
            rejects (SourceFunctionTypes.internSource {initial with canonical := {initial.canonical with sourceMaterial := some missing}} reference #[] #[])
            unless world.canonical.instances.size == initial.canonical.instances.size &&
                world.canonical.allocations.size == initial.canonical.allocations.size && world.canonical.bodies.size == initial.canonical.bodies.size do
              throw (IO.userError "type construction fabricated callable/allocation capabilities")
            count := count+1
  unless count > 0 do throw (IO.userError "no genuine nested function-item argument found")
  IO.println s!"PASS {count} nested FnDef keys/signatures, no fnptr erasure, idempotence and missing-header guard"
