import Miri.Input.CompilerConstantMachine
import empty_function.LocalUnit
namespace EmptyFunction.Literal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
set_option autoImplicit false
variable {K U Other : Type}
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem normalization_rejects_wrong_key (evidence : CompilerConstantEvidence)
    (callee : CallInstance) (original : MirConst)
    (different : (evidence.fnInstance == callee && evidence.original == original) = false) :
    normalizationFromEvidence #[evidence] callee original =
      .error (.query "missing compiler current-frame normalization evidence") := by
  simp [normalizationFromEvidence, different]
  rfl

theorem evaluation_rejects_wrong_key (evidence : CompilerConstantEvidence)
    (callee : CallInstance) (normalized : MirConst) (span : SpanRef)
    (different : (evidence.fnInstance == callee && evidence.normalized == normalized &&
      evidence.span == span) = false) :
    evaluationFromEvidence #[evidence] callee normalized span =
      .error (.query "missing compiler constant evaluation evidence") := by
  simp [evaluationFromEvidence, different]
  rfl

 theorem eval_unit (prepared : CompilerConstantQueries.Prepared)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (external : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (literal : ConstOperand) (unit : LocalLayout)
    (frame : LocalUnit.F) (frames : Array LocalUnit.F) (machine : MachineHooks.MachineState K U)
    (evidence : CompilerConstantEvidence)
    (body : frame.bodyIdentity.index = site.bodyIndex)
    (query : CompilerConstantQueries.lookup prepared site = .ok evidence)
    (value : literal.value = .Val .ZeroSized unit.ty)
    (normalization : normalizationFromEvidence #[evidence]
      frame.functionInstance literal.value = .ok literal.value) :
    CompilerConstantMachine.evalAt prepared site functions arithmetic external classify literal
      (some unit) none (LocalUnit.current frames frame machine) =
      .ok ⟨.immediate .uninit, unit⟩ (LocalUnit.current frames frame machine) := by
  simp [CompilerConstantMachine.evalAt, MachineHooks.currentFrame, LocalUnit.current,
    Stack.currentFrame?, body, query,
    ConstantMachine.evalOperandWithLayout, ConstantMachine.fromCompiler,
    evalConstOperandWithLayout, normalization, Except.mapError,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, Except.bind, pure, EStateM.pure]
  rw [value]
  rfl
theorem eval_query_error (prepared : CompilerConstantQueries.Prepared)
    (site : CompilerConstantQueries.Site)
    (functions : FunctionPointers.Hooks K U Other) (arithmetic : PointerArithmetic)
    (external : DefId → MachineHooks.M K U (Pointer Provenance))
    (classify : ConstantError → StepError) (literal : ConstOperand) (unit : LocalLayout)
    (frame : LocalUnit.F) (frames : Array LocalUnit.F) (machine : MachineHooks.MachineState K U)
    (body : frame.bodyIdentity.index = site.bodyIndex) (message : String)
    (query : CompilerConstantQueries.lookup prepared site = .error message) :
    CompilerConstantMachine.evalAt prepared site functions arithmetic external classify literal
      (some unit) none (LocalUnit.current frames frame machine) =
      .error (classify (.query message)) (LocalUnit.current frames frame machine) := by
  simp [CompilerConstantMachine.evalAt, MachineHooks.currentFrame, LocalUnit.current,
    Stack.currentFrame?, body, query, ConstantMachine.evalOperandWithLayout,
    ConstantMachine.fromCompiler, evalConstOperandWithLayout, Except.mapError,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, Except.bind,
    pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

end EmptyFunction.Literal
