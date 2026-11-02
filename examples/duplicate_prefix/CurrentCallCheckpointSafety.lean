import duplicate_prefix.CurrentCallCheckpointZeroFinish
import duplicate_prefix.CurrentCallCheckpointRejectedFinish
import duplicate_prefix.CurrentCallCheckpointAcceptedFinish
import duplicate_prefix.CurrentCallCheckpointCopiedRelease
import duplicate_prefix.DuplicatePrefixCompletedCallResult
namespace DuplicatePrefix.CurrentCallCheckpointSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallPostEntryCheckpoint
open ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place}

/-- One accepted continuation derives every actual helper, byte copy,
protector release, original-destination Bool store and root pop internally. -/
private theorem accepted (cp : Checkpoint options remaining span len count place) (limits : ExecutionMachine.Limits)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (nonzero : count≠0) (within : count≤len/2) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] cp.frame cp.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  obtain ⟨out⟩:=CurrentCallCheckpointRoot3.invoke cp limits budget dispatch nonzero
  obtain ⟨done,seed,helperTrace⟩:=CurrentCallCheckpointAsMutControl.prepare out nonzero within budget dispatch
  obtain ⟨returned⟩:=CurrentCallCheckpointAsMutRelease.invoke out done seed
  obtain ⟨source⟩:=CurrentCallCheckpointAsMutSource.current out done seed returned
  obtain ⟨B⟩:=CurrentCallCheckpointAcceptedBoolCurrent.invoke out done seed returned
  obtain ⟨access⟩:=CurrentCallCheckpointCopyAccess.invoke out done seed returned source nonzero within
  have statuses:=CurrentCallCheckpointCopyAccess.completed out done seed returned source access
  obtain ⟨copied⟩:=CurrentCallCheckpointCopyPrefix.of_steps out done seed returned budget dispatch statementFuel statementEq nonzero within statuses.1 statuses.2
  obtain ⟨Q⟩:=CurrentCallCheckpointCopiedQ.current out done seed returned source access copied within
  obtain ⟨target⟩:=CurrentCallCheckpointCopiedBoolCurrent.invoke out done seed returned source B access copied within
  obtain ⟨released⟩:=CurrentCallCheckpointCopiedRelease.release out done seed returned copied Q B target
  exact CurrentCallCheckpointAcceptedFinish.invoke out done seed returned copied target.current released

/-- The same post-entry resources cover every UInt64 count. The three cases
are the original program's guards, not representation-specific body proofs. -/
theorem execute (cp : Checkpoint options remaining span len count place) (limits : ExecutionMachine.Limits)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] cp.frame cp.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  by_cases zero : count=0
  · subst count
    exact CurrentCallCheckpointZeroFinish.invoke cp limits
  · by_cases within : count≤len/2
    · exact accepted cp limits budget dispatch statementFuel statementEq zero within
    · have gt : count>len/2:=by
        apply UInt64.lt_iff_toNat_lt.mpr
        have denied : ¬count.toNat≤(len/2).toNat:=fun bound=>within (UInt64.le_iff_toNat_le.mpr bound)
        omega
      obtain ⟨out⟩:=CurrentCallCheckpointRoot3.invoke cp limits budget dispatch zero
      exact CurrentCallCheckpointRejectedFinish.invoke out gt

/-- Prefix producers derive the literal original initialization equation.
One common body and the existing completed-trace adapter then establish the
original strong Result; no successful-operation premise belongs to validity. -/
theorem invoke (cp : Checkpoint options remaining span len count place) (limits : ExecutionMachine.Limits)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (statementFuel : Nat) (statementEq : limits.validation=statementFuel+1)
    (before : Before) (argument : DuplicatePrefixSliceArgument.Argument)
    (entry : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument len),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      (⟨⟨#[]⟩,before⟩ : MachineHooks.State MiriMemoryKind Machine.RootUser)=.ok () (Storage.withCurrent #[] cp.frame cp.machine)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place:=by
  obtain ⟨final,trace,terminal,empty⟩:=execute cp limits budget dispatch statementFuel statementEq
  exact DuplicatePrefixCompletedCallResult.of_trace options limits remaining span before argument len count place
    (Storage.withCurrent #[] cp.frame cp.machine) final entry ⟨by decide,rfl⟩ trace terminal
end
end DuplicatePrefix.CurrentCallCheckpointSafety
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointSafety" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common all-count original Result dependency {dependency}"
