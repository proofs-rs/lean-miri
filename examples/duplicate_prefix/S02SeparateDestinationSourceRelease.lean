import duplicate_prefix.S02ConcreteSourceReleasePacket
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.S02SeparateDestinationSourceRuntime
import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.GeneralBorrowBothProtectorRelease

namespace DuplicatePrefix.S02SeparateDestinationSourceRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- From the original contract, the positive argument's active protector
really releases after the distinct concrete destination is protected. This
uses the full callback-capable source Positive, rather than Quiescent. -/
theorem active_source_release_after_real_protect
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
        (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
        (sourceTracker : MachineHooks.BorrowState),
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        let released := sourceEntry.allocation.extra.releaseProtector
          reference.tracker.global.nextPointerTag sourceTracker.global.protectedTags
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
        after.machine.borrowTracker = some sourceTracker ∧
        after.machine.memory.live.find? (fun row => row.1 == reference.id) =
          some (reference.id,sourceEntry) ∧
        released.status = .Released ∧
        DuplicatePrefixBorrowContract.RuntimeFacts released.tree sourceTracker.global := by
  obtain ⟨reference,firstFresh,_argument,destination,secondFresh,tree,updated,protect,_bytes,_length,_mutable,
      _final,_finish⟩ :=
    S02SeparateDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      different returnTag returnConcrete limits.retag
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra finalTree}
  obtain ⟨_oldChild,_oldRaw,_same,_parent,_offset,_length,sourceLive,enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  obtain ⟨same,raw,parent,offset,length,_source,_selected,_maximum,runtimeInitial⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference
      input.contract.runtime input.contract.resources
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have headroom : reference.entry.allocation.extra.nodes.size+1 < 65536 := by
    have room := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    have room' : reference.entry.allocation.extra.nodes.size+16 < 65536 := by
      simpa only using room
    omega
  obtain ⟨child,node,lookup,present,sameTag,hidden,runtime,⟨positive⟩,active,roots,order,short⟩ :=
    S02ConcreteSourceReleasePacket.release_ready reference.entry.allocation.extra reference.tracker
      ({} : FrameState) reference.id runtimeInitial raw headroom
  have treeEq : finalTree = GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker raw.parentTag raw.offset raw.len := by
    rw [parent,offset,length]
  rw [←treeEq] at lookup present runtime positive active roots order short
  have trackerEq : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have globalEq : destination.tracker.global =
      TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh :=
    congrArg MachineHooks.BorrowState.global trackerEq
  change DuplicatePrefixBorrowContract.RuntimeFacts finalTree
    (TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh) at runtime
  change DuplicatePrefixBorrowAuthorization.Positive finalTree
    (TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh).protectedTags
    (some child) (some raw.selected) raw.maximum raw.offset raw.len at positive
  rw [←globalEq] at runtime positive
  have separate : destination.id ≠ reference.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have pointer := congrArg (fun p : Pointer (Option Provenance) => p.provenance) physical
    simp only [Pointer.withOptionalProvenance] at pointer
    have concrete : destination.pointer.provenance =
        .concrete input.contract.destination.id returnTag :=
      (Option.some.inj pointer).trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    have destId : destination.id = input.contract.destination.id := binding.1.symm
    simpa only [destId,same] using Ne.symm different
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have positiveCurrent : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      destination.tracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len := by
    change DuplicatePrefixBorrowAuthorization.Positive finalTree destination.tracker.global.protectedTags
      (some child) (some raw.selected) raw.maximum reference.offset len
    simpa only [offset,length] using positive
  obtain ⟨sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry separate sourceLive runtime
      (some child) (some raw.selected) raw.maximum reference.offset len positiveCurrent
  obtain ⟨runtimeTracker,runtimeTrackerAfter,_runtimeLive,runtimeAfter⟩ :=
    S02SeparateDestinationSourceRuntime.runtime_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry separate sourceLive runtime
  have sameTracker : runtimeTracker = sourceTracker :=
    Option.some.inj (runtimeTrackerAfter.symm.trans trackerAfter)
  rw [sameTracker] at runtimeAfter
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra sourceTracker.global := by
    exact runtimeAfter
  have sourcePositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
      sourceTracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len := positiveAfter
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
      reference.offset (reference.offset+len) := by
    change GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write
      reference.offset (reference.offset+len)
    simpa only [offset,length] using active
  have released := GeneralBorrowBothProtectorRelease.release sourceEntry.allocation.extra sourceTracker.global
    sourceRuntime reference.tracker.global.nextPointerTag child raw.selected raw.maximum reference.offset len
    sourcePositive node present hidden lookup roots order short sourceActive
  refine ⟨reference,firstFresh,destination,secondFresh,tree,updated,sourceEntry,sourceTracker,
    protect,trackerAfter,liveAfter,released.1,released.2.1⟩

end
end DuplicatePrefix.S02SeparateDestinationSourceRelease

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceRelease.active_source_release_after_real_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination active-release dependency {dependency}"
