import duplicate_prefix.CurrentCallZeroCountSafety
import duplicate_prefix.CurrentCallRejectedSafety
import duplicate_prefix.CurrentCallAcceptedSafety

/-! The original conditional safety result for every count with a positive
source length. Ordinary admission and the empty source remain separate
coverage obligations. -/
namespace DuplicatePrefix.CurrentCallPositiveSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false

/-- Every UInt64 count follows its actual zero, rejected, or accepted path. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  by_cases zero : count = 0
  · subst count
    exact CurrentCallZeroCountSafety.invoke input stackReady memoryReady positive
  · by_cases outside : len.toNat/2 < count.toNat
    · exact CurrentCallRejectedSafety.invoke input stackReady memoryReady positive count outside
    · have within : count ≤ len/2 := UInt64.le_iff_toNat_le.mpr (by
        have bounded : count.toNat ≤ len.toNat/2 := by omega
        simpa using bounded)
      exact CurrentCallAcceptedSafety.invoke input stackReady memoryReady positive count zero within

end DuplicatePrefix.CurrentCallPositiveSafety
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallPositiveSafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved positive-call safety dependency {dependency}"
