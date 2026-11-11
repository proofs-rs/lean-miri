import Miri.Input.CompilerGlobals
import Miri.Interpreter.Instance

/-! Exact instance_kind_json schema mirrors pinned ty/instance.rs. No shim or
generic argument is collapsed to its definition ID. -/
namespace Miri.Input.CompilerInstance
open Lean Miri.Interpreter
/-- Instance queries need only this canonical table; constructing a full lowering
context here would repeatedly copy unrelated type and allocation IDs. -/
def source (instances : Array InstanceNode) (id : Nat) : Except String InstanceNode := do
  let some identity := instances[id]? | throw s!"compiler instance ID {id} out of bounds"
  pure identity

/-- Only the operation requesting the instance kind reads this field. -/
def kindOf (instances : Array InstanceNode) (id : CallInstance) :
    Except String CallInstanceKind := do
  pure (← source instances id).instanceKind

/-- Generic arguments belong to their canonical instance and are read on demand. -/
def argsOf (instances : Array InstanceNode) (id : CallInstance) :
    Except String (Array MIR.GenericArg) := do
  pure (← source instances id).genericArgs

def definitionOf (instances : Array InstanceNode) (id : CallInstance) :
    Except String MIR.DefId := do
  return (← kindOf instances id).defId

/-- Resolve the exact Item identity required by upstream constructors. No new
instance or generic-argument identity is synthesized at an interpreter event. -/
def item (instances : Array InstanceNode) (definition : MIR.DefId)
    (args : Array MIR.GenericArg) : Except String CallInstance := do
  let mut found := none
  for id in [:instances.size] do
    if (← kindOf instances id) == .Item definition then
      if (← argsOf instances id) == args then
        if found.isSome then throw "duplicate canonical Item instance identity"
        found := some id
  let some id := found | throw "exact compiler Item instance is absent"
  pure id

end Miri.Input.CompilerInstance
