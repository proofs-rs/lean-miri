import Miri.Input.CompilerConstantQueries
import Miri.Interpreter.ConstantMachine

namespace Miri.Input.CompilerConstantMachine
open Miri.ABI Miri.Memory Miri.Interpreter

def evalAt (prepared : CompilerConstantQueries.Prepared) (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K User Other) (arithmetic : PointerArithmetic)
    (externStatic : MIR.DefId → MachineHooks.M K User (Pointer Provenance))
    (classify : ConstantError → StepError)
    (constant : MIR.ConstOperand) (known : Option LocalLayout := none)
    (checkKnown : Option (LocalLayout → LocalLayout → MachineHooks.M K User Bool) := none) :
    MachineHooks.M K User (OpTy Provenance) := do
  let frame ← MachineHooks.currentFrame
  unless frame.bodyIdentity.index == site.bodyIndex do
    throw (.invalidProgram "constant operand belongs to another canonical body")
  let query := CompilerConstantQueries.lookup prepared site
  let actual := ConstantMachine.fromCompiler functions arithmetic externStatic
    (fun callee original => do
      let evidence ← query.mapError ConstantError.query
      normalizationFromEvidence #[evidence] callee original)
    (fun callee normalized span => do
      let evidence ← query.mapError ConstantError.query
      evaluationFromEvidence #[evidence] callee normalized span)
  ConstantMachine.evalOperandWithLayout prepared.runtime actual classify constant known checkKnown

end Miri.Input.CompilerConstantMachine
