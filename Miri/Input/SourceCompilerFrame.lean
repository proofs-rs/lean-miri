import Miri.Input.SourceCompilerWorld
import Miri.Interpreter.Stack

/-! Canonical body access shared by frame diagnostics and compiler leaves.
Source installation validates MIR once. These queries preserve the exact
instance/body identity without lowering MIR or searching by equal syntax. -/
namespace Miri.Input.SourceCompilerFrame
open Miri.Interpreter

def body (world : SourceCompilerWorld.World) (callee : CallInstance)
    (identity : BodyIdentity) (mir : MIR.Body) : Except String Body := do
  let index ← SourceCompilerWorld.bodyId world callee
  unless index == identity.index do throw "full-instance/canonical body identity mismatch"
  let some actual := world.canonical.bodies[index]? | throw "canonical body identity is absent"
  unless actual.mir == mir do throw "canonical body/content mismatch"
  return actual

def definitionCrate (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Nat := do
  let node ← SourceCompilerWorld.node world callee
  let some definition := world.canonical.definitions[node.instanceKind.defId]?
    | throw "frame full-instance definition absent from shared compiler table"
  return definition.crateIndex
end Miri.Input.SourceCompilerFrame
