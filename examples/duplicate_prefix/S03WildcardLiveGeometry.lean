import duplicate_prefix.S03WildcardLiveState
import duplicate_prefix.S03LiveEmptyCapacity

namespace DuplicatePrefix.S03WildcardLiveGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Both actual constructors consume at most two nodes and retain backing
capacity; the wildcard argument's additional root is distinct from old roots. -/
theorem same_allocation {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (distinct : original.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.entry.allocation.extra)
    (headroom : original.entry.allocation.extra.nodes.size+2 < 65536)
    (first : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next original.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (slot : WildcardHitPoolRoot.Slot original.entry.allocation.extra)
    (tag : BorTag) (concrete : original.pointer.provenance = .concrete original.id tag)
    (positive : DuplicatePrefixBorrowAuthorization.Positive (slot.after original.tracker.global.nextPointerTag)
      (S03LiveEmptyState.next original.tracker first).global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree (slot.after original.tracker.global.nextPointerTag)
      (S03LiveEmptyState.next original.tracker first) tag original.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
      (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
      (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.nodes.size ≤ original.entry.allocation.extra.nodes.size+2 ∧ written.roots.toList.Nodup ∧
      written.locations.size = original.entry.allocation.extra.locations.size := by
  obtain ⟨_,current,currentOrder,currentDistinct,currentRoom,_,tagFresh,_⟩ :=
    S03WildcardLiveState.facts original runtime first slot headroom distinct order
  let input := S03WildcardLiveState.input original first slot tag concrete tagFresh positive
  have result := S03LiveEmptyInitGeometry.return_geometry input current currentDistinct currentOrder currentRoom second tag concrete
  have capacity := S03LiveEmptyCapacity.return_capacity input current currentDistinct currentOrder currentRoom second tag concrete
  have growth := slot.size original.tracker.global.nextPointerTag
  have bound : slot.growth ≤ 1 := by cases slot <;> simp [WildcardHitPoolRoot.Slot.growth]
  have upper : (slot.after original.tracker.global.nextPointerTag).nodes.size+1 ≤ original.entry.allocation.extra.nodes.size+2 := by omega
  refine ⟨Nat.le_trans result.1 upper,?_,capacity⟩
  let tree := GeneralBorrowRawFnEntryArgument.finalTree (slot.after original.tracker.global.nextPointerTag)
    (S03LiveEmptyState.next original.tracker first) tag original.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
    (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
    (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have roots : written.roots = (slot.after original.tracker.global.nextPointerTag).roots := result.2
  change written.roots.toList.Nodup
  rw [roots]
  exact currentDistinct

end
end DuplicatePrefix.S03WildcardLiveGeometry
