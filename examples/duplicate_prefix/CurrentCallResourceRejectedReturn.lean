import duplicate_prefix.CurrentCallResourceRejectedPrefix
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.CurrentCallResourceSameHeap
import duplicate_prefix.CurrentCallResourceEntryRelease
namespace DuplicatePrefix.CurrentCallResourceRejectedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags:=RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked:=model.unchecked
  have noGc:=model.noGc
  rw [(actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with
    unchecked:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.1.trans unchecked,
    noGc:=by rw [(actual_fields options () (remaining+1) span).terminators];exact flags.2.trans noGc}
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C) {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

/-- The rejected guard consumes the SAME post-Len semantic resources and
completes the actual root return. The public caller derives this resource
packet from the actual Len operations, rather than assuming their outcomes. -/
theorem complete {bData bOwner}
    (B : UniformWindow returned.machine (CurrentCallResourceLenReturn.postTracker out ready) bData bOwner C.physical.id C.physical.offset.toNat 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window returned.machine place)
    (pointer : physical.pointer=C.physical.pointer) (physicalId : physical.id=C.physical.id)
    (physicalOffset : physical.offset=C.physical.offset)
    (binding : CandidateCallBindings.WindowBinding returned.machine physical.pointer physical.id physical.offset.toNat 1)
    (parentIssued : SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out ready) C.physical.id
      B.allocation B.precise.completion C.V.pointer.grant)
    (parentBinding : PointerBinds B.allocation C.V.pointer)
    (released : CurrentCallResourceCurrentRelease.Released B (CurrentCallResourceEntryRelease.borrowFrame out)
      C.V.pointer.grant physical.offset physical.entry)
    (originalStop : root.frame.returnContinuation=.stop true)
    (originalVarargs : root.frame.vaList=#[])
    (originalDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩)
    (gt : count>len/2) :
    ∃ final,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧ final.stack.frames=#[] := by
  obtain ⟨frame,guardTrace,body,identity,callee,extra,destination,continuation,varargs,localsIdentity,size,located,slot0,immediate⟩:=
    CurrentCallResourceRejectedPrefix.invoke returned gt
  let m1:=RootZeroCompleteState.tick options remaining span returned.machine
  let m2:=RootZeroCompleteState.tick options remaining span m1
  let machine:=RootZeroCompleteState.tick options remaining span m2
  have memory : machine.memory=returned.machine.memory:=by
    unfold machine m2 m1 RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
  have addresses : machine.user.addresses=returned.machine.user.addresses:=by
    unfold machine m2 m1 RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  let currentB:=CurrentCallResourceSameHeap.window memory B
  let currentPhysical:=CurrentCallResourceSameHeap.scalar memory addresses physical
  let currentReleased:=CurrentCallResourceSameHeap.released memory released
  have model:=tick_model options remaining span m2 (tick_model options remaining span m1
    (tick_model options remaining span returned.machine (CurrentCallResourceLenFacts.model returned)))
  have enabled : machine.borrowTracker=some (CurrentCallResourceLenReturn.postTracker out ready):=by
    unfold machine m2 m1 RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact returned.tracked
  obtain ⟨thread,oldActive,top⟩:=returned.active
  have active : machine.threads.activeThread?=some thread:=by
    unfold machine m2 m1 RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact oldActive
  obtain ⟨rootBody,rootIdentity,rootCallee,clocks,rootDestination,rootContinuation,rootVarargs⟩:=CurrentCallResourceLenFacts.root_metadata returned
  have frameTracked : frame.extra.borrowTracker=some (CurrentCallResourceEntryRelease.borrowFrame out):=by
    rw [extra,(CurrentCallResourceLenFacts.metadata returned).2.2.2.1,returned.shape.extra]
    exact (CurrentCallResourceEntryFacts.metadata out).2.2.2.2.2.2.2.1
  have beforeExtras : returned.machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras:=by
    rw [returned.flags.extras,returned.helper.extras]
    change (CurrentCallResourceSharedStage.machine out).user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
    unfold CurrentCallResourceSharedStage.machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rw [CurrentCallResourceEntryFacts.user_eq out]
    rfl
  have extras : machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras:=by
    unfold machine m2 m1 RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact beforeExtras
  have windowReady : CurrentCallBoolProtection.WindowReady machine currentPhysical.id currentPhysical.offset.toNat 1:=by
    change CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1
    rw [physicalId,physicalOffset]
    exact C.ready.transport extras
  obtain ⟨final,finish,terminal,empty⟩:=CurrentCallResourceRootFinish.finish options limits remaining span place C.V currentB currentPhysical
    (CurrentCallResourceSameHeap.binding memory addresses binding) physicalId (congrArg UInt64.toNat physicalOffset)
    (pointer.trans C.returnPointer) (CurrentCallResourceSameHeap.issued memory parentIssued) parentBinding frame
    (CurrentCallResourceEntryRelease.borrowFrame out) currentReleased model enabled frameTracked thread active
    (body.trans rootBody) located size ((congrArg (fun e=>e.dataRace) extra).trans clocks)
    (continuation.trans (rootContinuation.trans originalStop)) (varargs.trans (rootVarargs.trans originalVarargs)) immediate false slot0
    (by rw [destination,rootDestination];exact originalDestination) windowReady C.validationFuel C.validationEq
  exact ⟨final,SuccessfulTrace.append returned.trace (SuccessfulTrace.append guardTrace finish),terminal,empty⟩
end
end DuplicatePrefix.CurrentCallResourceRejectedReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceRejectedReturn" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual rejected root return dependency {dependency}"
