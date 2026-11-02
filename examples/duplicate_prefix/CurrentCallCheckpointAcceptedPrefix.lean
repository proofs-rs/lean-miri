import duplicate_prefix.CurrentCallCheckpointCopyPrefix
import duplicate_prefix.RootSuccessToReturn
namespace DuplicatePrefix.CurrentCallCheckpointAcceptedPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options remaining span len count place limits}
  {checkpoint : CurrentCallPostEntryCheckpoint.Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output checkpoint limits)
  (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done)
  (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)
/-- Cleanup after the actual accepted byte copy reaches the true Return block. -/
theorem reaches_true :
    ∃ frame,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] copied.frame copied.machine)
      (Storage.withCurrent #[] {frame with location:=.mir ⟨10,0⟩}
        (SourceControl.accounted (config options (remaining+1) span).terminators (Storage.withCurrent #[] frame copied.machine)).machine) ∧
      RootSuccessCleanupFacts.Shape copied.frame frame RootCompilerFacts.boolLayout (.scalar (.fromBool true)):=by
  have valid (index : Fin 25) : index.val<copied.frame.locals.size:=by rw [copied.size];exact index.isLt
  have stored (index : Fin 25) (row : LocalState Provenance LocalLayout)
      (found : copied.frame.locals[index.val]?=some row) : copied.frame.locals[index.val]'(valid index)=row:=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans found)
  have slot0 : copied.frame.locals[0]?=some ⟨.live (.immediate .uninit),none⟩:=by
    rw [copied.keep 0 (by decide),CurrentCallCheckpointAsMutFacts.other out done seed returned 0 (by decide),
      CurrentCallCheckpointDefaultControl.Done.other done 0 (by decide),done.input.facts.slot0]
    exact CurrentCallCheckpointLenFacts.zero_slot checkpoint out.result
  have slot15:= (copied.keep 15 (by decide)).trans (CurrentCallCheckpointAsMutFacts.slot15 out done seed returned)
  obtain ⟨body,identity,callee,clocks,_,_,_⟩:=CurrentCallCheckpointAsMutFacts.metadata out done seed returned
  have mode : (CurrentCallCheckpointAsMutReturn.postTracker seed).retagMode=.Default:=CurrentCallCheckpointDefaultControl.mode out
  exact RootSuccessToReturn.reaches_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span copied.machine copied.model) checkpoint.model.debugOff checkpoint.validationFuel checkpoint.validationEq
    #[] copied.frame copied.machine copied.size _ _ _ _ _
    (congrArg LocalState.value (stored ⟨0,by decide⟩ _ slot0)) (congrArg LocalState.layout (stored ⟨0,by decide⟩ _ slot0))
    (congrArg LocalState.value (stored ⟨15,by decide⟩ _ slot15))
    (congrArg LocalState.value (stored ⟨17,by decide⟩ _ copied.slot17)) (congrArg LocalState.layout (stored ⟨17,by decide⟩ _ copied.slot17))
    (congrArg LocalState.value (stored ⟨18,by decide⟩ _ copied.slot18))
    (congrArg LocalState.value (stored ⟨19,by decide⟩ _ copied.slot19))
    (congrArg LocalState.value (stored ⟨21,by decide⟩ _ copied.slot21))
    (congrArg LocalState.value (stored ⟨24,by decide⟩ _ copied.slot24))
    (copied.body.trans body) (copied.identity.trans identity) (copied.callee.trans callee) copied.location
    ((congrArg (fun extra=>extra.dataRace) copied.extra).trans clocks)
    (CurrentCallCheckpointAsMutReturn.postTracker seed) copied.tracked mode copied.model.ghostOff copied.model.shallow
    copied.model.unchecked copied.model.noGc copied.model.fixedScheduler
end
end DuplicatePrefix.CurrentCallCheckpointAcceptedPrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAcceptedPrefix" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted resource cleanup dependency {dependency}"
