import Miri.Input.Reader.Generics
import Miri.Interpreter.Instance

namespace Miri.Input.Reader.AllocationFunctionReader
open Lean Miri.MIR

def read (catalog : Catalog) (typeCount : Nat) (allocations : Array AllocationNode)
    (instances : Array (Except String Miri.Interpreter.CallInstance)) :
    MIRReader.Decode (SharedTable (Except String AllocationFunctionData)) := do
  let values ← catalog.array (← catalog.field catalog.root "allocations" "$") "$.allocations"
  unless values.size == allocations.size do throw "allocation function table size mismatch"
  let mut result := #[]
  for (node,index) in allocations.toList.zipIdx do
    let some (.function source) := node.data | result := result.push none; continue
    let some input := values[index]? | throw "allocation function source absent"
    let path := s!"$.allocations[{index}]"
    let value ← try
        let some instanceResult := instances[source.instanceId]? | throw "global function instance ID absent"
        let callee ← instanceResult
        let definition ← GenericReader.definition catalog (← catalog.field input "instance_def_id" path) path
        let argsId ← GenericReader.arguments catalog typeCount (← catalog.field input "generic_args" path) path
        let state ← get
        let args ← state.arguments.lookup argsId |>.mapError (fun id => s!"invalid allocation function argument list {id}")
        unless definition == callee.defId do throw "global function/full-instance definition mismatch"
        unless args == callee.args do throw "global function/full-instance generic arguments mismatch"
        pure (.ok ⟨source.instanceId,source.definitionId,callee⟩)
      catch reason => pure (.error reason)
    result := result.push (some value)
  return result

end Miri.Input.Reader.AllocationFunctionReader
