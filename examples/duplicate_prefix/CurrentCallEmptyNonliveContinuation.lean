import duplicate_prefix.CurrentCallEmptyNonliveBodyControl
import duplicate_prefix.CurrentCallEmptyCounterContinuation
namespace DuplicatePrefix.CurrentCallEmptyContinuation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- One nonzero continuation for every actual metadata-backed absent source.
Its source protector is released by the common ledger classifier, not a
source-kind-specific MIR body or a fabricated source allocation. -/
theorem nonlive {options remaining span place machine tracker data owner id offset original B physical}
    (core : Core options remaining span place machine tracker data owner id offset original B physical)
    (limits : ExecutionMachine.Limits) (root : RootFrame)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (sourceFrame : FrameState) (borrow : core.borrowFrame=sourceFrame.addProtector id core.node.tag)
    (stop : root.frame.returnContinuation=.stop true)
    (destination : root.frame.returnPlace.toRuntimePlace=⟨.memory place.mplace,place.layout⟩) (varargs : root.frame.vaList=#[])
    (sourceId : AllocId) (sourceTag : BorTag) (metadataTag : Option BorTag) (base sourceOffset count : UInt64)
    (nonnull : base+sourceOffset≠0) (countNonzero : count≠0)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory sourceId metadataTag)
    (absent : machine.memory.live.find? (fun row=>row.1==sourceId)=none)
    (cached : machine.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (sourceBelow : sourceTag.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (room : tracker.global.nextPointerTag.value.toNat+4<2^64)
    (protectorsBelow : ∀row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (dynamicFuel validationFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (dispatchEq : limits.callDispatch=budget+1)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (top : core.thread.topUserRelevantFrame=some 0) :
    let updated:=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
    ∃final,SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (CurrentCallEmptyProtocolControl.frame root updated sourceFrame count id core.node.tag) machine) final ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () final=(final,.ok false) ∧final.stack.frames=#[] := by
  dsimp only
  let updated:=(RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete sourceId sourceTag) (Size.ofBytes (base+sourceOffset))) 0 ActualReferenceMetadata.reference).imm
  obtain ⟨result,post,nextTracker,trace,body,identity,callee,extra,returnPlace,continuation,va,_,size,location,slot,immediate,
    memory,tracked,mode,global,nextNat,ghost,shallow,race,fixed,unchecked,noGc,addresses,types,backend,extras,⟨thread,active⟩⟩:=
    CurrentCallEmptyNonliveBodyControl.to_return options limits remaining span root raw sourceFrame id core.node.tag
      machine core.model origins tracker core.tracked sourceTag sourceId metadataTag base sourceOffset count nonnull countNonzero
      metadata absent cached sourceBelow room protectorsBelow fresh dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq tagRoom
      core.thread core.activeThread top
  have nextMode : nextTracker.retagMode=.Default := by
    obtain ⟨old,enabled,default⟩:=core.model.defaultTracker
    have same : old=tracker:=Option.some.inj (enabled.symm.trans core.tracked)
    subst old
    exact mode.trans default
  have model : DuplicatePrefixCallModel.Model options remaining span post:=
    ⟨core.model.debugOff,core.model.preciseOff,core.model.implicitOff,ghost,shallow,⟨nextTracker,tracked,nextMode⟩,race,
      backend.trans core.model.noBackend,by rw [types];exact core.model.metadata,
      fixed,unchecked,noGc,core.model.nullComparator,core.model.sourceMatches⟩
  obtain ⟨Q,P,next,sourceEq,borrowEq,nodeEq⟩:=core.counter_view post nextTracker memory addresses extras global
    (by rw [nextNat];omega) model tracked thread active
  have facts:=CurrentCallEmptyProtocolControl.metadata root updated sourceFrame count id core.node.tag
  have ready : Ready options remaining span place post nextTracker data owner id offset original Q P result:={
    toCore:=next,
    frameTracked:=by rw [borrowEq,borrow,extra];exact facts.2.2.2.2.2.2.2.1,
    body:=body.trans (facts.1.trans root.body),location:=location,size:=size,
    noClocks:=by rw [extra];exact facts.2.2.2.2.2.2.1.trans root.noClocks,
    stop:=continuation.trans (facts.2.2.2.1.trans stop),
    varargs:=va.trans (facts.2.2.2.2.2.1.trans varargs),immediate:=immediate,value:=false,slot0:=slot,
    destination:=by rw [returnPlace,facts.2.2.2.2.1];exact destination}
  obtain ⟨final,returned,terminal,empty⟩:=finish ready limits validationFuel validationEq
  exact ⟨final,SuccessfulTrace.append trace returned,terminal,empty⟩
end
end DuplicatePrefix.CurrentCallEmptyContinuation
