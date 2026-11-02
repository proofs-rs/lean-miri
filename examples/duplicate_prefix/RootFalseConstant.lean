import duplicate_prefix.LiteralConstant
namespace DuplicatePrefix.RootFalseConstant
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def site : CompilerConstantQueries.Site :=
  ⟨RootBody.reflected.body.identity.index,⟨5,2⟩,#[.field "kind",.field "rvalue",.field "operand",.field "constant"]⟩
def constant : ConstOperand := ⟨⟨18⟩,none,.Val (.Scalar (.Int 0 1)) 0⟩

theorem normalization : normalizationFromEvidence (LiteralConstant.evidence site)
    RootBody.reflected.functionInstance (.Val (.Scalar (.Int 0 1)) 0) = .ok (.Val (.Scalar (.Int 0 1)) 0) := by
  with_unfolding_all rfl

theorem conversion (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
    (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser)) :
    valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries (.Scalar (.Int 0 1)) 0
      (some RootCompilerFacts.boolLayout) none state =
    .ok ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩ state := by
  with_unfolding_all rfl

theorem operand
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨5,2⟩)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "operand") (.Constant constant) (some RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (.fromBool false)),RootCompilerFacts.boolLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  exact LiteralConstant.operand_at options limits remaining span source debugOff site (OperandPath.rvalue "operand") (by simp [site, OperandPath.rvalue])
    (.Scalar (.Int 0 1)) 0 ⟨18⟩ (some RootCompilerFacts.boolLayout) (.scalar (.fromBool false))
    RootCompilerFacts.boolLayout normalization conversion framesBefore frame machine bodyIndex location callee

#print axioms normalization
#print axioms conversion
#print axioms operand
end DuplicatePrefix.RootFalseConstant
