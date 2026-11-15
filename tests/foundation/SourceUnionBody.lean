import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceMirLowering
open Lean Miri Miri.Input Miri.Frontend.Foundation

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine union entry source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let initial ← IO.ofExcept (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let (initial,word) ← IO.ofExcept (SourcePhysical.intern initial (.primitive "uint" "u32"))
  let mut world := initial
  for (name,arguments,field) in [("byte",#[],0),("word",#[],1),("generic",#[MIR.GenericArg.Type word],0)] do
    let [declaration] := (source.declarations.filter (·.path == name)).toList
      | throw (IO.userError "genuine declaration absent")
    let (next,callee) ← IO.ofExcept (SourceCompilerWorld.internItem source.declarations world ⟨declaration.definition,arguments⟩)
    world ← IO.ofExcept (SourceMirLowering.derive next callee)
    let bodyId ← IO.ofExcept (SourceCompilerWorld.bodyId world callee)
    let some body := world.canonical.bodies[bodyId]? | throw (IO.userError "derived body absent")
    let mut found := 0
    for block in body.mir.basicBlocks do
      for statement in block.statements do
        if let .Assign _ (.Aggregate (.Adt definition variant actualArgs annotation active) operands) := statement.kind then
          unless variant == 0 && annotation.isNone && active == some field && operands.size == 1 do
            throw (IO.userError "union active field/operand changed during lowering")
          let some raw := world.canonical.definitions[definition]? | throw (IO.userError "ADT raw identity absent")
          let some physical := source.physical | throw (IO.userError "source type declarations absent")
          unless physical.definitions.any (fun row => row.raw == raw && row.kind == "Union") do
            throw (IO.userError "lowered aggregate did not retain genuine union identity")
          unless actualArgs == arguments do throw (IO.userError "full union generic substitution changed")
          found := found+1
    unless found == 1 do throw (IO.userError s!"{name}: actual union aggregate missing")
  IO.println "genuine union bodies derived through fixed MIR with field0/field1/generic active-field identity"
