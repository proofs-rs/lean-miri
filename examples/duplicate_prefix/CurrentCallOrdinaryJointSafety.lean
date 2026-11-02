import duplicate_prefix.CurrentCallOrdinaryJointEntry
import duplicate_prefix.CurrentCallCheckpointSafety

/-! The positive source and LIVE return branch of the adopted current-input
domain uses the one common all-count continuation after its actual entry. -/
namespace DuplicatePrefix.CurrentCallOrdinaryJointSafety
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open CurrentCallResourceNormalization CurrentCallOrdinaryInput
set_option autoImplicit false

/-- The original strong Result for every count, with only initial representation
branch selection in addition to the adopted input. -/
theorem live {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (positive : len ≠ 0)
    (sourceLive : CurrentCallOrdinaryJointEntry.sourceIsLive before argument len = true)
    (returnLive : (before.memory.live.find? (fun row => row.1 == input.returnFamily.allocation)).isSome = true)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨checkpoint, entry⟩ := CurrentCallOrdinaryJointEntry.live input positive sourceLive returnLive count
  have workPositive : 0 < DuplicatePrefixCallSpecification.work before len := by
    unfold DuplicatePrefixCallSpecification.work
    omega
  have dispatchPositive : 0 < limits.callDispatch := by
    have := input.resources.executionFuel.1
    omega
  have validationPositive : 0 < limits.validation := by
    have := input.resources.executionFuel.2.2.2
    omega
  obtain ⟨budget, dispatch⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : limits.callDispatch ≠ 0)
  obtain ⟨statementFuel, statementEq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : limits.validation ≠ 0)
  exact CurrentCallCheckpointSafety.invoke checkpoint limits budget dispatch statementFuel statementEq before argument entry

end DuplicatePrefix.CurrentCallOrdinaryJointSafety
