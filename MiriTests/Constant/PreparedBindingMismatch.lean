import Miri.Input.CompilerConstantMachine

/-! One compiler/runtime owner makes source mixing unrepresentable. Numeric
constant IDs still select evidence only: exact semantic query keys are checked. -/
open Miri Miri.Input Miri.Interpreter Miri.MIR

example (owner : RuntimeProgram) : owner.runtime.source = owner.program.input := rfl
example (owner : RuntimeProgram) (program : LoweredProgram) :
    (owner.withProgram program).runtime.source = owner.runtime.source := rfl
example (prepared : CompilerConstantQueries.Prepared) :
    prepared.runtime.source = prepared.program.input := rfl

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

#print axioms normalization_rejects_wrong_key
#print axioms evaluation_rejects_wrong_key
