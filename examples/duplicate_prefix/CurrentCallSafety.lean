import duplicate_prefix.CurrentCallPositiveSafety
import duplicate_prefix.CurrentCallEmptyZeroCountSafety
import duplicate_prefix.CurrentCallEmptyNonzeroSafety

/-! Conditional current-call coverage. The original Proposed representation
and explicit machine readiness remain hypotheses; ordinary admission is open. -/
namespace DuplicatePrefix.CurrentCallSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every length and count returns the unchanged original Result under the
same proposed call domain and explicit stack/profile readiness. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  by_cases empty : len=0
  · subst len
    by_cases zero : count=0
    · subst count
      exact CurrentCallEmptyZeroCountSafety.invoke input stackReady memoryReady
    · exact CurrentCallEmptyNonzeroSafety.invoke input stackReady memoryReady count zero
  · exact CurrentCallPositiveSafety.invoke input stackReady memoryReady (Nat.pos_of_ne_zero (fun zero => empty (UInt64.toNat_inj.mp zero))) count
end DuplicatePrefix.CurrentCallSafety

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSafety" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved conditional current-call safety dependency {dependency}"
