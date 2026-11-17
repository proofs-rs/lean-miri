import duplicate_prefix.S03LiveEmptyInitGeometry
import duplicate_prefix.GeneralBorrowRawFnEntryOrder

namespace DuplicatePrefix.S03LiveEmptyCapacity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The exact protected return Read/constructor/Write keeps the backing tree's
capacity. This supplies current physical Destination metadata after uninit. -/
theorem return_capacity {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.locations.size = input.entry.allocation.extra.locations.size := by
  obtain ⟨raw,parentTag,offset,length,_,_⟩ := S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  obtain ⟨current,capacity,growth,roots,_,_,_,child,tagged,⟨positive⟩,_⟩ :=
    GeneralBorrowRawFnEntryResources.resources input.entry.allocation.extra input.tracker {} input.id runtime raw
  have ordered := GeneralBorrowRawFnEntryOrder.order input.entry.allocation.extra input.tracker {} input.id runtime raw order
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker raw.parentTag raw.offset raw.len
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker raw.tagRoom) input.tracker.global.nextPointerTag
  have short : tree.nodes.size < 65536 := Nat.lt_of_le_of_lt growth headroom
  obtain ⟨contract,_,_⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind tree global current
    input.tracker.global.nextPointerTag child raw.selected raw.maximum tagged (Size.ofBytes raw.offset) (Size.ofBytes raw.len) .Write
    .VisitChildrenOfAccessed raw.offset raw.len positive (by rw [roots];exact distinct) (fun _ _ => ordered) short (Nat.le_refl _) (Nat.le_refl _)
  simpa only [tree,global,parentTag,offset,length] using contract.capacity.trans capacity

/-- Full live same-allocation initialization keeps the original tree capacity,
including the initial ZERO constructor. The observer is the produced witness
returned by S03LiveEmptyInit.enters, not a new caller premise. -/
theorem same_allocation {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (distinct : original.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.entry.allocation.extra)
    (headroom : original.entry.allocation.extra.nodes.size+2 < 65536)
    (first : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next original.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag) (slot : ConcreteEmptyPoolEntry.Input original.entry.allocation.extra parentTag original.tracker.global.nextPointerTag)
    (tag : BorTag) (concrete : original.pointer.provenance = .concrete original.id tag)
    (positive : DuplicatePrefixBorrowAuthorization.Positive slot.after (S03LiveEmptyState.next original.tracker first).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree slot.after (S03LiveEmptyState.next original.tracker first) tag original.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
      (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
      (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.locations.size = original.entry.allocation.extra.locations.size := by
  obtain ⟨_,current,currentOrder,roots,currentRoom,_⟩ :=
    S03LiveEmptyState.facts original runtime first parentTag slot headroom order
  have result := return_capacity (S03LiveEmptyState.input original first parentTag slot tag concrete positive)
    current (by change slot.after.roots.toList.Nodup;rw [roots];exact distinct) currentOrder currentRoom second tag concrete
  exact result.trans (S04ZeroChildMetadata.capacity _ _ _ slot)

end
end DuplicatePrefix.S03LiveEmptyCapacity
