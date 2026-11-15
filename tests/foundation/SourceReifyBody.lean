import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceMirLowering
open Lean Miri Miri.Input Miri.Frontend.Foundation

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine reification entry source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let initial ← IO.ofExcept (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let (initial,word) ← IO.ofExcept (SourcePhysical.intern initial (.primitive "uint" "u16"))
  let mut world := initial
  for (name,arguments,safety) in [("safe",#[],MIR.Safety.Safe),("unsafe_pointer",#[],.Unsafe),
      ("generic",#[MIR.GenericArg.Type word],.Safe)] do
    let [declaration] := (source.declarations.filter (·.path == name)).toList
      | throw (IO.userError "genuine declaration absent")
    let (next,callee) ← IO.ofExcept (SourceCompilerWorld.internItem source.declarations world ⟨declaration.definition,arguments⟩)
    world ← IO.ofExcept (SourceMirLowering.derive next callee)
    let bodyId ← IO.ofExcept (SourceCompilerWorld.bodyId world callee)
    let some body := world.canonical.bodies[bodyId]? | throw (IO.userError "derived body absent")
    let some mir := source.genericMir | throw (IO.userError "generic MIR source absent")
    let [sourceBody] := (mir.bodies.filter (·.definition == declaration.definition)).toList
      | throw (IO.userError "genuine source body absent")
    let mut annotations : Array (Option Nat) := #[]
    for block in sourceBody.blocks do
      for statement in block.statements do
        if let .assign _ (.pointerCoercion _ (.constant operand) _ _) := statement.kind then
          annotations := annotations.push operand.userType
    let mut actualAnnotations : Array (Option Nat) := #[]
    let mut found := 0
    for block in body.mir.basicBlocks do
      for statement in block.statements do
        if let .Assign destination (.Cast (.PointerCoercion (.ReifyFnPointer actualSafety) coercionSource) operand target) := statement.kind then
          let .Constant operand := operand | throw (IO.userError "source function operand ceased to be constant")
          actualAnnotations := actualAnnotations.push operand.userType
          unless actualSafety == safety && coercionSource == .Implicit &&
              body.mir.locals[destination.localId]? == some target do
            throw (IO.userError "function reification safety/target identity changed")
          let some node := world.canonical.types[target]? | throw (IO.userError "reification target absent")
          let .functionPointer signature _ := node.shape | throw (IO.userError "reification target is not function pointer")
          unless signature.safety == safety do throw (IO.userError "reification target safety differs")
          if name == "generic" then
            unless signature.inputs == #[word] && signature.output == word do
              throw (IO.userError "generic signature substitution changed")
          found := found+1
    unless found == 1 && actualAnnotations == annotations do
      throw (IO.userError s!"{name}: actual reification/opaque annotation changed")
    if name == "generic" then
      unless annotations.any Option.isSome do throw (IO.userError "genuine generic annotation coverage absent")
  IO.println "genuine safe/unsafe/generic function reification derived through fixed MIR Cast"
