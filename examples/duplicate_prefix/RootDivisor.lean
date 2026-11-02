import duplicate_prefix.LiteralConstant
namespace DuplicatePrefix.RootDivisor
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def site : CompilerConstantQueries.Site :=
  ⟨RootBody.reflected.body.identity.index,⟨4,0⟩,#[.field "kind",.field "rvalue",.field "right",.field "constant"]⟩
def constant : ConstOperand := ⟨⟨17⟩,none,.Val (.Scalar (.Int 2 8)) 5⟩

theorem normalization : normalizationFromEvidence (LiteralConstant.evidence site)
    RootBody.reflected.functionInstance (.Val (.Scalar (.Int 2 8)) 5) = .ok (.Val (.Scalar (.Int 2 8)) 5) := by
  with_unfolding_all rfl

theorem conversion (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
    (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser)) :
    valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries (.Scalar (.Int 2 8)) 5
      (some RootCompilerFacts.usizeLayout) none state =
    .ok ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 2))),RootCompilerFacts.usizeLayout⟩ state := by
  with_unfolding_all rfl

theorem operand
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨4,0⟩)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "right") (.Constant constant) (some RootCompilerFacts.usizeLayout)
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 2))),RootCompilerFacts.usizeLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  exact LiteralConstant.operand_at options limits remaining span source debugOff site (OperandPath.rvalue "right") (by simp [site, OperandPath.rvalue])
    (.Scalar (.Int 2 8)) 5 ⟨17⟩ (some RootCompilerFacts.usizeLayout) (.scalar (.fromScalarInt (.ofUInt64 2)))
    RootCompilerFacts.usizeLayout normalization conversion framesBefore frame machine bodyIndex location callee

#print axioms normalization
#print axioms conversion
#print axioms operand
end DuplicatePrefix.RootDivisor
