import duplicate_prefix.CurrentCallCheckpointRejectedControl
import duplicate_prefix.CurrentCallCheckpointRoot3Release
import duplicate_prefix.CurrentCallCheckpointReturnTransport
import duplicate_prefix.CurrentCallResourceRootFinish

namespace DuplicatePrefix.CurrentCallCheckpointRejectedFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CurrentCallPostEntryCheckpoint CurrentCallCheckpointRoot3
open CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem tick_model (options remaining span before)
    (model : DuplicatePrefixCallModel.Model options remaining span before) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span before):=by
  have flags:=RootZeroCompleteState.tick_flags options remaining span before
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}

/-- Common rejecting body completion consumes the joint output and performs
the original destination store after the two actual root release passes. -/
theorem invoke {options remaining span len count place limits}
    {checkpoint : Checkpoint options remaining span len count place} (out : Output checkpoint limits)
    (gt : count>len/2) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] checkpoint.frame checkpoint.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  obtain ⟨frame,guard,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,location,slot0,immediate⟩:=
    CurrentCallCheckpointRejectedControl.invoke out gt
  obtain ⟨released⟩:=CurrentCallCheckpointRoot3Release.release out
  let beforeReturn:=RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span out.machine))
  have memory : beforeReturn.memory=out.machine.memory:=rfl
  have addresses : beforeReturn.user.addresses=out.machine.user.addresses:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : beforeReturn.user.payload.payload.user.runtime.extras=out.machine.user.payload.payload.user.runtime.extras:=by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  let current:=CurrentCallCheckpointReturnTransport.move out.target.current beforeReturn memory addresses extras
  let currentReleased:=CurrentCallCheckpointReturnTransport.released out.target.current beforeReturn memory addresses extras checkpoint.borrowFrame released
  have binding : CandidateCallBindings.WindowBinding beforeReturn current.physical.pointer current.physical.id current.physical.offset.toNat 1:=by
    simpa only [current.physicalId,current.physicalOffset] using current.binding
  have model:=tick_model options remaining span _ (tick_model options remaining span _ (tick_model options remaining span _ out.model))
  obtain ⟨thread,active,_⟩:=out.active
  have activeNow : beforeReturn.threads.activeThread?=some thread:=active
  have enabled : beforeReturn.borrowTracker=some out.tracker:=out.tracked
  obtain ⟨rootBody,rootIdentity,rootCallee,rootClocks,rootDestination,rootContinuation,rootVarargs⟩:=
    CurrentCallCheckpointLenFacts.root_metadata checkpoint out.result
  obtain ⟨final,finish,terminal,empty⟩:=CurrentCallResourceRootFinish.finish_pointer options limits remaining span place
    current.original current.originalId current.window current.physical binding current.physicalId current.physicalOffset
    current.originalPointer.symm current.originalIssued current.originalBinding frame checkpoint.borrowFrame currentReleased model enabled
    (by rw [extra];exact out.frameTracked) thread activeNow (body.trans rootBody) location size
    (by rw [extra];exact rootClocks) (continuation.trans rootContinuation) (varargs.trans rootVarargs) immediate false slot0
    (by rw [destination,rootDestination];exact checkpoint.destination) (by simpa only [current.physicalId,current.physicalOffset] using current.profile) checkpoint.validationFuel checkpoint.validationEq
  exact ⟨final,SuccessfulTrace.append out.trace (SuccessfulTrace.append guard finish),terminal,empty⟩

end
end DuplicatePrefix.CurrentCallCheckpointRejectedFinish
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointRejectedFinish" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common rejecting finish dependency {dependency}"
