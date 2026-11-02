import duplicate_prefix.CurrentCallResourceAcceptedSafety
import duplicate_prefix.CurrentCallResourceRejectedSafety
import duplicate_prefix.CurrentCallResourceZeroSafety
namespace DuplicatePrefix.CurrentCallResourceSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- Every count follows the actual zero, rejecting, or copying branch from the
same initial uniform live resources. This is not an ordinary-domain coverage
claim; the original strong call result and all its clauses are unchanged. -/
theorem invoke {options remaining span before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : Conditions options remaining span #[] (CurrentCallResourceEntry.root before #[] place race)
      before tracker data owner id offset len W place)
    (ready : CurrentCallResourceBodyReadiness.Ready C) (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (physicalSource : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (storageRoom : W.allocation.len+64<2^64)
    (sourceProfile : CurrentCallBoolProtection.WindowReady before id (UInt64.ofNat offset).toNat len.toNat)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer W.pointer.value) len count place:=by
  by_cases zero : count=0
  · subst count
    exact CurrentCallResourceZeroSafety.invoke limits race C ready stackReady
  · by_cases accepted : count≤len/2
    · exact CurrentCallResourceAcceptedSafety.invoke limits race C ready stackReady budget dispatch statementFuel statementEq
        physicalSource storageRoom sourceProfile count zero accepted
    · have rejected : count>len/2:=UInt64.lt_iff_toNat_lt.mpr (by
        have notle : ¬count.toNat≤(len/2).toNat:=by intro bound;exact accepted (UInt64.le_iff_toNat_le.mpr bound)
        omega)
      exact CurrentCallResourceRejectedSafety.invoke limits race C ready stackReady budget dispatch count rejected
end
end DuplicatePrefix.CurrentCallResourceSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSafety" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved all-count uniform resource safety dependency {dependency}"
