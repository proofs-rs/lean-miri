import duplicate_prefix.S03LiveEmptyState

namespace DuplicatePrefix.S03LiveEmptyInitGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Exact geometry of the return protection Read/constructor/Write. It consumes
one node at most and keeps the old roots; both accesses preserve node metadata. -/
theorem return_geometry {before : Before} {place : MPlaceTy Provenance}
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
    written.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
    written.roots = input.entry.allocation.extra.roots := by
  obtain ⟨raw,parentTag,offset,length,_,_⟩ := S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  obtain ⟨_,capacity,growth,roots,_⟩ := GeneralBorrowRawFnEntryResources.resources input.entry.allocation.extra input.tracker {} input.id runtime raw
  simp only [parentTag,offset,length] at capacity growth roots
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed
  dsimp only
  refine ⟨?_,?_⟩
  · rw [congrArg (fun value : BorrowTree => value.nodes.size) frame]
    exact growth
  · rw [congrArg BorrowTree.roots frame]
    exact roots

/-- The two actual constructors in live same-allocation initialization consume
at most two nodes in total and retain the initial root list. The current
observer below is the produced witness returned by S03LiveEmptyInit.enters. -/
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
    written.nodes.size ≤ original.entry.allocation.extra.nodes.size+2 ∧ written.roots = original.entry.allocation.extra.roots := by
  obtain ⟨_,current,currentOrder,roots,currentRoom,_⟩ :=
    S03LiveEmptyState.facts original runtime first parentTag slot headroom order
  have result := return_geometry (S03LiveEmptyState.input original first parentTag slot tag concrete positive)
    current (by change slot.after.roots.toList.Nodup;rw [roots];exact distinct) currentOrder currentRoom second tag concrete
  have growth := ConcreteEmptyPoolEntryNext.node_size slot
  have bound : ConcreteEmptyPoolEntryNext.growth slot ≤ 1 := by
    cases selected : slot.slot <;> simp only [ConcreteEmptyPoolEntryNext.growth,selected] <;> omega
  have upper : slot.after.nodes.size+1 ≤ original.entry.allocation.extra.nodes.size+2 := by omega
  exact ⟨Nat.le_trans result.1 upper,result.2.trans roots⟩

/-- The original sixteen-tag budget leaves fourteen slots after actual
argument and return-protector registration. No new full Resources is assumed. -/
theorem tag_margin (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+16 < 2^64)
    (first : tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next tracker first).global.nextPointerTag.value < 18446744073709551615) :
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next tracker first) second)
      (S03LiveEmptyState.next tracker first).global.nextPointerTag
    global.nextPointerTag.value.toNat+14 < 2^64 := by
  have one := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag first
  change (S03LiveEmptyState.next tracker first).global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at one
  have two := GenericFunctionEntryNumerics.successor_value (S03LiveEmptyState.next tracker first).global.nextPointerTag second
  change (TypedRetagEmpty.successorTag (S03LiveEmptyState.next tracker first).global.nextPointerTag second).value.toNat+14 < 2^64
  omega

end
end DuplicatePrefix.S03LiveEmptyInitGeometry
