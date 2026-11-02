import duplicate_prefix.S02DisjointFnEntryTree
import duplicate_prefix.S02DisjointAccessPositive
import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.GeneralBorrowFreshRegistration

namespace DuplicatePrefix.S02SameAllocationProtectSource
open Miri Miri.Input Miri.Memory Miri.ABI Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A disjoint source window keeps full Positive capability through the
same-allocation return FnEntry and its actual uninitializing Write. Both
operations are derived from the current data-only return/source packets. -/
theorem positive (current : DuplicatePrefixCallSpecification.Before) (place : MPlaceTy Provenance)
    (destination : DuplicatePrefixReturnPlaceInput.Input current place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (headroom : destination.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id tag)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : destination.offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ destination.offset.toNat)
    (old : Positive destination.entry.allocation.extra destination.tracker.global.protectedTags source selected maximum lower width) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker tag destination.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker fresh)
      destination.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
      (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    Nonempty (Positive written global.protectedTags source selected maximum lower width) := by
  obtain ⟨raw,parentTag,offsetEq,lenEq,_selected,_maximum⟩ := S03ReturnProtectionRaw.packet destination runtime distinct order headroom fresh tag concrete
  have complete := GeneralBorrowForestTagHighWater.complete destination.entry.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  have freshTag := (GenericFunctionTagFormation.fresh_above destination.entry.allocation.extra
    destination.tracker.global.protectedTags destination.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag
    complete (Nat.le_refl _)).2.1
  obtain ⟨registered⟩ := GeneralBorrowFreshRegistration.positive destination.entry.allocation.extra destination.tracker.global.protectedTags
    destination.tracker.global.nextPointerTag .StrongProtector freshTag source selected maximum lower width old
  have rawOutside : raw.offset.toNat+raw.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ raw.offset.toNat := by
    simpa only [offsetEq,lenEq,UInt64.toNat_one] using outside
  obtain ⟨afterSource⟩ := S02DisjointFnEntryTree.positive destination.entry.allocation.extra destination.tracker ({} : FrameState)
    destination.id runtime raw source selected maximum lower width rawOutside registered
  obtain ⟨post,capacity,growth,roots,_held,_frame,_fresh,child,tagged,⟨afterDestination⟩,_active⟩ :=
    GeneralBorrowRawFnEntryResources.resources destination.entry.allocation.extra destination.tracker ({} : FrameState) destination.id runtime raw
  have postOrder := GeneralBorrowRawFnEntryOrder.order destination.entry.allocation.extra destination.tracker ({} : FrameState)
    destination.id runtime raw order
  simp only [parentTag,offsetEq,lenEq] at afterSource post capacity growth roots tagged afterDestination postOrder
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker tag destination.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker fresh)
    destination.tracker.global.nextPointerTag
  have short : tree.nodes.size < 65536 := by
    dsimp only [tree]
    omega
  have postDistinct : tree.roots.toList.Nodup := by rw [roots];exact distinct
  obtain ⟨contract,_runtime,_destination⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind tree global post
    destination.tracker.global.nextPointerTag child raw.selected raw.maximum tagged (Size.ofBytes destination.offset) (Size.ofBytes 1)
    .Write .VisitChildrenOfAccessed destination.offset 1 afterDestination postDistinct (fun _ _ => postOrder) short (Nat.le_refl _) (Nat.le_refl _)
  exact S02DisjointAccessPositive.positive_from_source_contract tree destination.tracker.global.nextPointerTag child raw.selected raw.maximum
    tagged (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed
    source selected maximum lower width afterSource post.formed.well afterDestination.bounds outside contract

end DuplicatePrefix.S02SameAllocationProtectSource

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameAllocationProtectSource.positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
