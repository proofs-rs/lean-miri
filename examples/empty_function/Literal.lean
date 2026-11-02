import Miri.Input.CompilerConstantMachine
import empty_function.LocalUnit
namespace EmptyFunction.Literal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
set_option autoImplicit false
variable {K U Other : Type}
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
 theorem eval_unit {prepared : CompilerConstantQueries.Prepared} {runtime : RuntimeMetadata}
    (binding : CompilerConstantQueries.Binding prepared runtime)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (external : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (literal : ConstOperand) (unit : LocalLayout)
    (frame : LocalUnit.F) (frames : Array LocalUnit.F) (machine : MachineHooks.MachineState K U)
    (compatible : binding.compatible = true)
    (body : frame.bodyIdentity.index = site.bodyIndex)
    (location : frame.location = .mir site.location)
    (value : literal.value = .Val .ZeroSized unit.ty)
    (normalization : normalizationFromEvidence
      ((prepared.evidence.filter (fun entry => entry.site == site)).map (fun entry => entry.query))
      frame.functionInstance literal.value = .ok literal.value) :
    CompilerConstantMachine.evalAtBound binding site functions arithmetic external classify literal
      (some unit) none (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit, unit⟩ (LocalUnit.current frames frame machine) := by
  simp [CompilerConstantMachine.evalAtBound, MachineHooks.currentFrame, LocalUnit.current,
    Stack.currentFrame?, compatible, body, location,
    ConstantMachine.evalOperandWithLayout, ConstantMachine.fromCompiler,
    evalConstOperandWithLayout, normalization,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  rw [value]
  rfl
end EmptyFunction.Literal
