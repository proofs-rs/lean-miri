import Miri.Input.CompilerGlobals
import Miri.Interpreter.Instance

/-! Exact instance_kind_json schema mirrors pinned ty/instance.rs. No shim or
generic argument is collapsed to its definition ID. -/
namespace Miri.Input.CompilerInstance
open Lean Miri.Interpreter
/-- Read one immutable canonical identity row without expanding its references. -/
def source (ctx : LowerContext) (id : Nat) : Except String InstanceNode := do
  let some identity := ctx.instances[id]? | throw s!"compiler instance ID {id} out of bounds"
  pure identity

/-- Query envelopes preserve the serialization-local instance ID. -/
def decode (ctx : LowerContext) (tables : CompilerTables) (j : Json) :
    Except String (CallInstance × CompilerTables) := do
  let id ← match j with
    | .num _ => j.getNat?
    | _ => (← j.getObjVal? "instance_id").getNat?
  let _ ← source ctx id
  pure (id,tables)

/-- Only the operation requesting the instance kind reads this field. -/
def kindOf (ctx : LowerContext) (tables : CompilerTables) (id : CallInstance) :
    Except String CallInstanceKind := do
  pure (← source ctx id).instanceKind

/-- Generic arguments belong to their canonical instance and are read on demand. -/
def argsOf (ctx : LowerContext) (tables : CompilerTables) (id : CallInstance) :
    Except String (Array MIR.GenericArg) := do
  pure (← source ctx id).genericArgs

def definitionOf (ctx : LowerContext) (tables : CompilerTables) (id : CallInstance) :
    Except String MIR.DefId := do
  return (← kindOf ctx tables id).defId

/-- Resolve the exact Item identity required by upstream constructors. No new
instance or generic-argument identity is synthesized at an interpreter event. -/
def item (ctx : LowerContext) (tables : CompilerTables) (definition : MIR.DefId)
    (args : Array MIR.GenericArg) : Except String CallInstance := do
  let mut found := none
  for id in [:ctx.instances.size] do
    if (← kindOf ctx tables id) == .Item definition then
      if (← argsOf ctx tables id) == args then
        if found.isSome then throw "duplicate canonical Item instance identity"
        found := some id
  let some id := found | throw "exact compiler Item instance is absent"
  pure id

end Miri.Input.CompilerInstance
