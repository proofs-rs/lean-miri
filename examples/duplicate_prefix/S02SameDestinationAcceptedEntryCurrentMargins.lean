import duplicate_prefix.S02SameDestinationReady
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02ProtectUninitNodes

namespace DuplicatePrefix.S02SameDestinationAcceptedEntryCurrentMargins
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Both argument and return construction consume at most two original nodes
and tags. The actual same-allocation post-uninit tree therefore has the local
margins needed by the following shared/len helper, without another budget. -/
theorem current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len) place)
    (sameId : destination.id = reference.id)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (returnTag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id returnTag) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
      (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.nodes.size+4 < 65536 ∧ written.nodes.size+4 ≤ 4294967295 ∧ global.nextPointerTag.value.toNat+3 < 18446744073709551615 ∧ written.locations.size = destination.entry.allocation.byteSize := by
  obtain ⟨_,raw,parent,offset,length,_source,_selected,_maximum,runtimeInitial⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
  have firstFacts := GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker ({} : FrameState)
    reference.id runtimeInitial raw
  have firstGrowth := firstFacts.2.2.1
  simp only [parent,offset,length] at firstGrowth
  obtain ⟨_child,_raw,_id,_parent,_offset,_len,sourceLive,_enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have destEntry : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree
      reference.entry.allocation.extra reference.tracker tag reference.offset len)} := by
    have live := destination.live
    rw [sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans sourceLive))
  have destGrowth : destination.entry.allocation.extra.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 := by
    rw [destEntry]
    exact firstGrowth
  obtain ⟨runtime,roots,order,nodes,_fresh⟩ := S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  obtain ⟨returnRaw,returnParent,returnOffset,returnLength,_selected,_maximum⟩ :=
    S03ReturnProtectionRaw.packet destination runtime roots order nodes secondFresh returnTag concrete
  have secondFacts := GeneralBorrowRawFnEntryResources.resources destination.entry.allocation.extra destination.tracker
    ({} : FrameState) destination.id runtime returnRaw
  have secondGrowth := secondFacts.2.2.1
  have writtenNodes := (S02ProtectUninitNodes.frame destination.entry.allocation.extra destination.tracker returnRaw).1
  simp only [returnParent,returnOffset,returnLength] at secondGrowth writtenNodes
  have writtenSize : ((GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1).performBorrowAccessRange
      (.concrete destination.tracker.global.nextPointerTag) (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
      (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree.nodes.size =
      (GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1).nodes.size := by
    exact congrArg UniValMap.size writtenNodes
  obtain ⟨secondRuntime,secondCapacity,_secondGrowth,secondRoots,_held,_frame,_fresh,returnChild,returnTagged,⟨secondPositive⟩,_activity⟩ := secondFacts
  have secondOrder := GeneralBorrowRawFnEntryOrder.order destination.entry.allocation.extra destination.tracker ({} : FrameState)
    destination.id runtime returnRaw order
  simp only [returnParent,returnOffset,returnLength] at secondRuntime secondCapacity secondRoots returnTagged secondPositive secondOrder
  let retagged := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have retaggedShort : retagged.nodes.size < 65536 := by dsimp only [retagged];omega
  have retaggedDistinct : retagged.roots.toList.Nodup := by rw [secondRoots];exact roots
  have writeContract := (GeneralBorrowConcreteRowReadRange.access_runtime_kind retagged global secondRuntime
    destination.tracker.global.nextPointerTag returnChild returnRaw.selected returnRaw.maximum returnTagged
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed destination.offset 1 secondPositive
    retaggedDistinct (fun _ _ => secondOrder) retaggedShort (Nat.le_refl _) (Nat.le_refl _)).1
  have destinationCapacity : destination.entry.allocation.extra.locations.size = destination.entry.allocation.byteSize :=
    (congrArg Size.mk destination.borrowSize).trans destination.size.symm
  have fullCapacity := writeContract.capacity.trans (secondCapacity.trans destinationCapacity)
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have originalRoom := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  dsimp only at originalRoom
  have trackerEq : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have firstTag : destination.tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+1 := by
    rw [trackerEq]
    exact GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
  have secondTag := GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag secondFresh
  have refTracker : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tagRoom : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by
    simpa only [←refTracker] using input.contract.resources.tagRoom
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · omega
  · omega
  · change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat+3 < 18446744073709551615
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = destination.tracker.global.nextPointerTag.value.toNat+1 at secondTag
    rw [secondTag,firstTag]
    omega
  · exact fullCapacity

end
end DuplicatePrefix.S02SameDestinationAcceptedEntryCurrentMargins

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedEntryCurrentMargins.current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
