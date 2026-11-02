import duplicate_prefix.CurrentCallCheckpointAcceptedPrefix
import duplicate_prefix.CurrentCallCheckpointReturnTransport
import duplicate_prefix.CurrentCallResourceRootFinish
namespace DuplicatePrefix.CurrentCallCheckpointAcceptedFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallPostEntryCheckpoint
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
variable {options remaining span len count place limits}
  {cp : Checkpoint options remaining span len count place}
  (out : CurrentCallCheckpointRoot3.Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
  (seed : CurrentCallCheckpointAsMutControl.Helper out done) (returned : CurrentCallCheckpointAsMutReturn.Returned seed)
  (copied : CurrentCallCheckpointCopyPrefix.Copied out done seed returned)

/-- Common accepted control performs the original Bool store and root pop
from resources derived on this same actual copied machine. -/
theorem invoke (target : Return copied.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) place)
    (released : CurrentCallResourceCurrentRelease.Released target.window cp.borrowFrame
      target.original.grant target.physical.offset target.physical.entry) :
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] cp.frame cp.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  obtain ⟨frame,bodyTrace,shape⟩:=CurrentCallCheckpointAcceptedPrefix.reaches_true out done seed returned copied
  let machine:=RootZeroCompleteState.tick options remaining span copied.machine
  change SuccessfulTrace.Trace _ _ _ (Storage.withCurrent #[] {frame with location:=.mir ⟨10,0⟩} machine) at bodyTrace
  have memory : machine.memory=copied.machine.memory:=rfl
  have addresses : machine.user.addresses=copied.machine.user.addresses:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : machine.user.payload.payload.user.runtime.extras=copied.machine.user.payload.payload.user.runtime.extras:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  let current:=CurrentCallCheckpointReturnTransport.move target machine memory addresses extras
  let currentReleased:=CurrentCallCheckpointReturnTransport.released target machine memory addresses extras cp.borrowFrame released
  have binding : CandidateCallBindings.WindowBinding machine current.physical.pointer current.physical.id current.physical.offset.toNat 1:=by
    simpa only [current.physicalId,current.physicalOffset] using current.binding
  have model:=tick_model options remaining span copied.machine copied.model
  have enabled : machine.borrowTracker=some (CurrentCallCheckpointAsMutReturn.postTracker seed):=copied.tracked
  obtain ⟨thread,active⟩:=copied.active
  have activeNow : machine.threads.activeThread?=some thread:=active
  have returnedExtra : returned.root.extra=out.frame.extra:=by
    rw [returned.rootEq]
    exact done.input.extra
  have frameTracked : frame.extra.borrowTracker=some cp.borrowFrame:=by
    rw [shape.extra,copied.extra,returnedExtra]
    exact out.frameTracked
  obtain ⟨rootBody,rootIdentity,rootCallee,clocks,rootDestination,rootContinuation,rootVarargs⟩:=CurrentCallCheckpointAsMutFacts.metadata out done seed returned
  obtain ⟨_,_,_,_,lenDestination,lenContinuation,lenVarargs⟩:=CurrentCallCheckpointLenFacts.root_metadata cp out.result
  obtain ⟨final,finish,terminal,empty⟩:=CurrentCallResourceRootFinish.finish_pointer options limits remaining span place
    current.original current.originalId current.window current.physical binding current.physicalId current.physicalOffset
    current.originalPointer.symm current.originalIssued current.originalBinding {frame with location:=.mir ⟨10,0⟩} cp.borrowFrame currentReleased model enabled
    frameTracked thread activeNow (shape.body.trans (copied.body.trans rootBody)) rfl shape.size
    ((congrArg (fun extra=>extra.dataRace) (shape.extra.trans copied.extra)).trans clocks)
    (shape.continuation.trans (copied.continuation.trans (rootContinuation.trans lenContinuation)))
    (shape.varargs.trans (copied.varargs.trans (rootVarargs.trans lenVarargs)))
    (shape.immediate copied.immediate) true shape.output
    (by
      change frame.returnPlace.toRuntimePlace=_
      rw [shape.destination,copied.destination,rootDestination]
      change out.result.rootFrame.returnPlace.toRuntimePlace=_
      rw [lenDestination]
      exact cp.destination)
    (by simpa only [current.physicalId,current.physicalOffset] using current.profile) cp.validationFuel cp.validationEq
  exact ⟨final,SuccessfulTrace.append out.trace (SuccessfulTrace.append done.trace (SuccessfulTrace.append returned.trace
    (SuccessfulTrace.append copied.trace (SuccessfulTrace.append bodyTrace finish)))),terminal,empty⟩
end
end DuplicatePrefix.CurrentCallCheckpointAcceptedFinish
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAcceptedFinish" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common accepted finish dependency {dependency}"
