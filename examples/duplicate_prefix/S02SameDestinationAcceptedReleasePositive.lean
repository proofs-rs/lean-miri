import duplicate_prefix.S02DisjointReleaseFrame
import duplicate_prefix.S02ConstructorOutsideRow
import duplicate_prefix.GeneralBorrowBothProtectorRelease
import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens
namespace DuplicatePrefix.S02SameDestinationAcceptedReleasePositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixBorrowAuthorization GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The real hidden Read-helper release preserves a disjoint owner's complete capability. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (helper selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (helperPositive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags helper selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt helper = some node) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some helper) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : ActiveWithin tree helper .Write offset (offset+len))
    (source destinationSelected : Option UniIndex) (destinationMaximum : Option BorTag) (lower width : UInt64)
    (outside : (offset+len).toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ offset.toNat)
    (destination : Positive tree global.protectedTags source destinationSelected destinationMaximum lower width) :
    Nonempty (Positive (tree.releaseProtector tag global.protectedTags).tree global.protectedTags source destinationSelected destinationMaximum lower width) := by
  obtain ⟨done,afterRuntime,afterPositive,afterActive,frame,capacity⟩ := GeneralBorrowBothProtectorRelease.release tree global runtime
    tag helper selected maximum offset len helperPositive node present hidden tagged distinct order short active
  have kept := S02DisjointReleaseFrame.release tree global.protectedTags tag helper helper node tagged present hidden offset (offset+len)
    active active (fun location => Nonempty (Row tree location global.protectedTags source destinationSelected destinationMaximum))
    lower (lower+width) outside destination.rows runtime.formed.well
  refine ⟨{positive := destination.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩
  · rw [capacity];exact destination.bounds
  · intro anchor same
    rw [frame]
    exact destination.sourcePresent anchor same
  · intro same
    rw [frame]
    exact destination.wildcardRoot same
  · rw [frame]
    intro position valid nonempty start stop
    obtain ⟨row⟩ := kept position valid nonempty start stop
    exact S02ConstructorOutsideRow.context tree tree.tagMapping _ _ global.protectedTags source destinationSelected destinationMaximum row
end DuplicatePrefix.S02SameDestinationAcceptedReleasePositive
