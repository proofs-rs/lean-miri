import Miri.Input.RuntimeArrayTypes

namespace Miri.Input.CompilerInstance
open Miri.Interpreter

def source (world : RuntimeArrayTypes.World) (id : InstanceId) : Except String InstanceArena.Key := do
  match ← world.instances.lookup id with
  | .material key | .constructed key => pure key

def kindOf (world : RuntimeArrayTypes.World) (id : CallInstance) : Except String CallInstanceKind :=
  return (← source world id).kind

def argsOf (world : RuntimeArrayTypes.World) (id : CallInstance) : Except String (Array MIR.GenericArg) :=
  return (← source world id).arguments

def definitionOf (world : RuntimeArrayTypes.World) (id : CallInstance) : Except String MIR.DefId :=
  return (← kindOf world id).defId

/-- Intern syntax only; the body and ABI providers remain separate capabilities. -/
def item (definition : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM CallInstance :=
  RuntimeArrayTypes.internInstance (.Item definition) args

end Miri.Input.CompilerInstance

/- Immutable source-table validation only; never a runtime instance fallback. -/
namespace Miri.Input.CompilerInstance.Material
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

end Miri.Input.CompilerInstance.Material
