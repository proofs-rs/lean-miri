import duplicate_prefix.S02ConcreteSourceWildcardReturnPacket
import duplicate_prefix.S02SeparateDestinationAuthorization
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S02ConcreteSourceWildcardAbsent
import duplicate_prefix.S02SeparateDestinationHiddenFrame
import duplicate_prefix.S02WildcardReturnRootNotPrimary

namespace DuplicatePrefix.S02ConcreteSourceWildcardArgumentIdentity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Contract formation of the exact wildcard return packet immediately after
the real positive concrete argument and wildcard protect+uninit operation. -/
theorem after_protection_argument_identity
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
      (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
          reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
      let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame (RawRootInvocation.machine #[] before)) =
          .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      destination.id = input.contract.destination.id ∧
      destination.entry = input.contract.destination.entry ∧
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag
        place (Storage.withCurrent #[] changed current) = .ok () after ∧
      ∃ packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame, packet.destination.id = destination.id := by
  obtain ⟨reference,firstFresh,argument,destination,destId,destEntry,_destOffset⟩ :=
    S02SeparateDestinationAuthorization.destination_input_after_argument id tag address len count
      input nonempty different
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  have wildcard : destination.pointer.provenance = .wildcard := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    rw [same]
    exact returnWildcard
  obtain ⟨tree,updated,protect,extra,bytes,length,mutable,maskWf,maskLen,pointers,capacity,
    writtenRuntime,writtenShort,writtenDistinct,writtenOrder,writtenExposed,oldTags,child,
    tagged,rootPush,⟨positive⟩,active,node,present,same,parentless,leaf,hidden⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags
      (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots order nodes secondFresh wildcard
      #[] changed owned frameBorrow #[] extras (by simp)
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags
    .VisitChildrenOfAccessed).tree
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let physical := S03ReturnWildcardMetadata.of_protection destination wildcard #[] changed owned secondFresh
    tree updated written extra bytes length mutable maskWf maskLen pointers capacity
  have absent := S02ConcreteSourceWildcardAbsent.written id tag address len input reference firstFresh
    destination destEntry secondFresh written oldTags
  have sourceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have separate : physical.id ≠ reference.id := by
    change destination.id ≠ reference.id
    rw [destId,sourceId]
    exact Ne.symm different
  have ownedTags : borrowFrame.protectedTags =
      #[(reference.id,reference.tracker.global.nextPointerTag),
        (physical.id,destination.tracker.global.nextPointerTag)] := rfl
  have hiddenFrame := S02SeparateDestinationHiddenFrame.of_absent written global borrowFrame
    reference.id physical.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag child node ownedTags writtenRuntime absent tagged present hidden
  have oldPositive := destination.borrow
  have binding := destination.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  rw [binding.1] at oldPositive
  have nonemptyRoots : 0 < destination.entry.allocation.extra.roots.size :=
    oldPositive.wildcardRoot rfl
  have notPrimary := S02WildcardReturnRootNotPrimary.after_push
    destination.entry.allocation.extra written child nonemptyRoots rootPush writtenDistinct
  have enabled : after.machine.borrowTracker = some
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := rfl
  have positive' : DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
      (some child) (some child) (some destination.tracker.global.nextPointerTag) destination.offset 1 :=
    positive.base
  have physicalExtra : physical.entry.allocation.extra = updated.extra := rfl
  let packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id reference.tracker.global.nextPointerTag borrowFrame := {
    destination := physical
    tracker := TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    enabled := enabled
    returnTag := destination.tracker.global.nextPointerTag
    child := child
    node := node
    owned := ownedTags
    tagged := by rw [physicalExtra,extra]; exact tagged
    present := by rw [physicalExtra,extra]; exact present
    same := same
    parentless := parentless
    leaf := leaf
    hidden := hidden
    hiddenFrame := by rw [physicalExtra,extra]; exact hiddenFrame
    runtime := by rw [physicalExtra,extra]; exact writtenRuntime
    positive := by rw [physicalExtra,extra]; exact positive'
    distinct := by rw [physicalExtra,extra]; exact writtenDistinct
    order := by rw [physicalExtra,extra]; exact writtenOrder
    exposed := by rw [physicalExtra,extra]; exact writtenExposed
    notPrimary := by rw [physicalExtra,extra]; exact notPrimary
    short := by rw [physicalExtra,extra]; exact writtenShort
    activity := by rw [physicalExtra,extra]; exact active }
  exact ⟨reference,firstFresh,destination,secondFresh,tree,updated,argument,destId,destEntry,protect,packet,rfl⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardArgumentIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardArgumentIdentity.after_protection_argument_identity) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard argument packet dependency {dependency}"
