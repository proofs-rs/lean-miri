import Miri.Input.CompilerConstantMachine
import Miri.Interpreter.ExecutionMachine

namespace Miri.Input.CompilerOperandSites
open Miri.Interpreter Miri.Memory

def current (id : Miri.MIR.ConstantId) : MachineHooks.M K User CompilerConstantQueries.Site := do
  let frame ← MachineHooks.currentFrame
  let .mir _ := frame.location | throw .expectedMirLocation
  return ⟨frame.bodyIdentity.index,id⟩

end Miri.Input.CompilerOperandSites
