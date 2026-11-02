import duplicate_prefix.CurrentCallResourceAcceptedPrefix
import duplicate_prefix.CurrentCallResourceRootFinish
import duplicate_prefix.CurrentCallResourceSameHeap
import duplicate_prefix.CurrentCallResourceEntryRelease
namespace DuplicatePrefix.CurrentCallResourceAcceptedReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open CanonicalConfigFacts ActualReferenceContext
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
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)

    (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned)

/-- The actual true-return control consumes current post-copy resources. The
outer caller constructs these from the same operations and copied heap. -/
theorem complete {bData bOwner}
    (B : UniformWindow copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) bData bOwner C.physical.id C.physical.offset.toNat 1 .ret)
    (physical : CurrentCallBoolScalarWrite.Window copied.machine place)
    (pointer : physical.pointer=C.physical.pointer) (physicalId : physical.id=C.physical.id)
    (physicalOffset : physical.offset=C.physical.offset)
    (binding : CandidateCallBindings.WindowBinding copied.machine physical.pointer physical.id physical.offset.toNat 1)
    (parentIssued : SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) C.physical.id
      B.allocation B.precise.completion C.V.pointer.grant)
    (parentBinding : PointerBinds B.allocation C.V.pointer)
    (released : CurrentCallResourceCurrentRelease.Released B (CurrentCallResourceEntryRelease.borrowFrame out)
      C.V.pointer.grant physical.offset physical.entry)
    (originalStop : root.frame.returnContinuation=.stop true) (originalVarargs : root.frame.vaList=#[])
    (originalDestination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩) :
    ∃ final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] result.rootFrame result.machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[]:=by
  obtain ⟨frame,bodyTrace,shape⟩:=CurrentCallResourceAcceptedPrefix.reaches_true done fresh valid15 seed returned copied
  let machine:=RootZeroCompleteState.tick options remaining span copied.machine
  change SuccessfulTrace.Trace _ _ _ (Storage.withCurrent #[] {frame with location:=.mir ⟨10,0⟩} machine) at bodyTrace
  have memory : machine.memory=copied.machine.memory:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
  have addresses : machine.user.addresses=copied.machine.user.addresses:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    rfl
  let currentB:=CurrentCallResourceSameHeap.window memory B
  let currentPhysical:=CurrentCallResourceSameHeap.scalar memory addresses physical
  let currentReleased:=CurrentCallResourceSameHeap.released memory released
  have model:=tick_model options remaining span copied.machine copied.model
  have enabled : machine.borrowTracker=some (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed):=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact copied.tracked
  obtain ⟨thread,oldActive⟩:=copied.active
  have active : machine.threads.activeThread?=some thread:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact oldActive
  have returnedExtra : returned.root.extra=result.rootFrame.extra:=by
    have actual:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.extra) returned.rootEq
    dsimp only [AsMutPtrReturn.writeFrame,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] at actual
    have defaultExtra:=congrArg (fun frame : CompilerFrameContext.ActualFrame=>frame.extra) done.frameEq
    dsimp only [CurrentCallResourceAsMutInvoke.defaultFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] at defaultExtra
    exact actual.trans (defaultExtra.trans done.input.extra)
  have frameTracked : frame.extra.borrowTracker=some (CurrentCallResourceEntryRelease.borrowFrame out):=by
    rw [shape.extra,copied.extra,returnedExtra,(CurrentCallResourceLenFacts.metadata result).2.2.2.1,result.shape.extra]
    exact (CurrentCallResourceEntryFacts.metadata out).2.2.2.2.2.2.2.1
  obtain ⟨rootBody,rootIdentity,rootCallee,clocks,rootDestination,rootContinuation,rootVarargs⟩:=CurrentCallResourceAsMutFacts.metadata done fresh valid15 seed returned
  obtain ⟨_,_,_,_,lenDestination,lenContinuation,lenVarargs⟩:=CurrentCallResourceLenFacts.root_metadata result
  have extras : machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras:=by
    unfold machine RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact copied.extras.trans (CurrentCallResourceCopyInputs.extras done fresh valid15 seed returned)
  have windowReady : CurrentCallBoolProtection.WindowReady machine currentPhysical.id currentPhysical.offset.toNat 1:=by
    change CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1
    rw [physicalId,physicalOffset]
    exact C.ready.transport extras
  obtain ⟨final,finish,terminal,empty⟩:=CurrentCallResourceRootFinish.finish options limits remaining span place C.V currentB currentPhysical
    (CurrentCallResourceSameHeap.binding memory addresses binding) physicalId (congrArg UInt64.toNat physicalOffset)
    (pointer.trans C.returnPointer) (CurrentCallResourceSameHeap.issued memory parentIssued) parentBinding
    {frame with location:=.mir ⟨10,0⟩} (CurrentCallResourceEntryRelease.borrowFrame out) currentReleased model enabled frameTracked thread active
    (shape.body.trans (copied.body.trans rootBody)) rfl shape.size
    ((congrArg (fun extra=>extra.dataRace) (shape.extra.trans copied.extra)).trans clocks)
    (shape.continuation.trans (copied.continuation.trans (rootContinuation.trans (lenContinuation.trans originalStop))))
    (shape.varargs.trans (copied.varargs.trans (rootVarargs.trans (lenVarargs.trans originalVarargs))))
    (shape.immediate copied.immediate) true shape.output
    (by change frame.returnPlace.toRuntimePlace=_;rw [shape.destination,copied.destination,rootDestination,lenDestination];exact originalDestination)
    windowReady C.validationFuel C.validationEq
  exact ⟨final,SuccessfulTrace.append done.trace (SuccessfulTrace.append returned.trace (SuccessfulTrace.append copied.trace
    (SuccessfulTrace.append bodyTrace finish))),terminal,empty⟩
end
end DuplicatePrefix.CurrentCallResourceAcceptedReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedReturn" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual accepted resource return dependency {dependency}"
