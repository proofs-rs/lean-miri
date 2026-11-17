import duplicate_prefix.LiteralConstant
namespace DuplicatePrefix.RootDivisionCheckTwo
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def constant : ConstOperand := ⟨⟨31⟩,none,.Val (.Scalar (.Int 2 8)) 5⟩

theorem conversion (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
    (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser)) :
    valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries (.Scalar (.Int 2 8)) 5
      none none state =
    .ok ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 2))),RootCompilerFacts.usizeLayout⟩ state := by
  with_unfolding_all rfl

theorem operand
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨3,1⟩)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      ()  (.Constant constant) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 2))),RootCompilerFacts.usizeLayout⟩
      (Storage.withCurrent framesBefore frame machine) := by
  exact LiteralConstant.operand_at options limits remaining span debugOff
    (.Scalar (.Int 2 8)) 5 ⟨31⟩ none (.scalar (.fromScalarInt (.ofUInt64 2)))
    RootCompilerFacts.usizeLayout conversion (Storage.withCurrent framesBefore frame machine)

#print axioms conversion
#print axioms operand
end DuplicatePrefix.RootDivisionCheckTwo
