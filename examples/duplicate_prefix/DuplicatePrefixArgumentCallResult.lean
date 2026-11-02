import duplicate_prefix.DuplicatePrefixCallResult
import duplicate_prefix.DuplicatePrefixSliceArgument

namespace DuplicatePrefix.DuplicatePrefixArgumentCallResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
noncomputable section

/-- The common actual call/return safety postcondition with the first scalar
encoded explicitly as a provenance-carrying pointer OR a provenance-free
integer. Neither input validity nor complete coverage is asserted here.
The canonical empty outer stack and Unit choice are the same as in the older
pointer-only result. Unsupported, fuel exhaustion and every interpreter error
remain excluded by the successful trace, normal return and NoErrors clauses. -/
def Result (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : DuplicatePrefixSliceArgument.Argument) (len count : UInt64)
    (place : MPlaceTy Provenance) : Prop :=
  let cfg := config options (remaining + 1) span
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨cfg, limits, fun _ _ => True⟩
  ∃ installed finalState,
    Call.initStackFrame (ExecutionMachine.callHooks cfg limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩, before⟩ = .ok () installed ∧
    SuccessfulTrace.Trace cfg limits installed finalState ∧
    ExecutionMachine.step cfg limits () finalState = (finalState, .ok false) ∧
    finalState.stack.frames = #[] ∧
    CallSafety.NoErrorsBeforeReturn context 1 installed ∧
    CallSafety.NoUBBeforeReturn context 1 installed ∧
    (∀ reachableState, SuccessfulTrace.Trace cfg limits installed reachableState →
      ∃ next continuing, ExecutionMachine.step cfg limits () reachableState = (next, .ok continuing))

/-- The earlier public pointer result is preserved exactly, not weakened or
reproved with a stronger caller premise. -/
theorem pointer_iff (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len count : UInt64) (place : MPlaceTy Provenance) :
    Result options limits remaining span before (.pointer pointer) len count place ↔
      DuplicatePrefixCallResult.Result options limits remaining span before pointer len count place := Iff.rfl

/-- The integer empty branch invokes the exact existing no-provenance first
argument. This is an encoding equality, not an assumption that FnEntry accepts
every empty pointer/metadata configuration. -/
theorem integer_empty_encoding (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (address : UInt64) :
    DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.integer address) 0 =
      EmptyRootArguments.first address := rfl

end
end DuplicatePrefix.DuplicatePrefixArgumentCallResult
