import duplicate_prefix.RootConstantStage
import duplicate_prefix.CanonicalConfigFacts

/-! Compose checked value conversion with the production constant and operand
machines. Executable constants have already been resolved by the input reader. -/
namespace DuplicatePrefix.LiteralConstant
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- `convert` is proved for the actual typed literal in each client. -/
theorem at_bound
    (literal : ConstValue) (ty : TyId) (refSpan : SpanRef)
    (known : Option LocalLayout) (immediate : Immediate Provenance) (layout : LocalLayout)
    (convert : ∀ (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
      (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (ConstantMachine.Context MiriMemoryKind Machine.RootUser)),
      valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries literal ty known none state =
        .ok ⟨.immediate immediate,layout⟩ state)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime
      functions arithmetic externStatic MemoryErrors.constant ⟨refSpan,none,.Val literal ty⟩ known none state =
    .ok ⟨.immediate immediate,layout⟩ state := by
  simp only [ConstantMachine.evalOperandWithLayout, ConstantMachine.evalValueWithLayout, Option.map_none]
  rw [convert]

theorem operand_at
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (literal : ConstValue) (ty : TyId) (refSpan : SpanRef)
    (known : Option LocalLayout) (immediate : Immediate Provenance) (layout : LocalLayout)
    (convert : ∀ (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
      (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
        (ConstantMachine.Context MiriMemoryKind Machine.RootUser)),
      valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries literal ty known none state =
        .ok ⟨.immediate immediate,layout⟩ state)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (.Constant ⟨refSpan,none,.Val literal ty⟩) known state =
    .ok ⟨.immediate immediate,layout⟩ state := by
  let config := PreparedContracts.actualConfig options () remaining span
  obtain ⟨externStatic,constantAt⟩ := (CanonicalConfigFacts.actual_fields options () remaining span).constantAt debugOff
  change config.operands.constant () ⟨refSpan,none,.Val literal ty⟩ known state = _
  rw [constantAt]
  exact at_bound literal ty refSpan known immediate layout convert config.functions config.arithmetic externStatic state

#print axioms operand_at
#print axioms at_bound
end DuplicatePrefix.LiteralConstant
