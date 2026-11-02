import duplicate_prefix.GeneralBorrowFreshReleaseLoop
import duplicate_prefix.GeneralBorrowExposedLeafRootUniqueSkip
namespace DuplicatePrefix.GeneralBorrowHomogeneousHiddenUniqueRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralRangeMapState RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Exact one-row source release adapter: the hidden active Unique root really
performs its associated Write while still protected, then takes the real hidden
exposure-update branch. -/
theorem release (tree : BorrowTree) (location : LocationTree) (capacity : UInt64)
    (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex) (node : TreeNode)
    (locations : tree.locations=homogeneous capacity location)
    (tagged : tree.indexOfTag tag=some anchor) (present : tree.nodeAt anchor=some node) (hidden : node.isExposed=false)
    (stored : location.perms.get anchor=some GeneralBorrowWildcardLeaf.unique)
    (callback : source_access_status (source_tree_access_at tree location (some anchor) .Write protections .SkipChildrenOfAccessed ⟨0,capacity⟩)=none) :
    tree.releaseProtector tag protections=
      ⟨{tree with locations:=(homogeneous capacity (source_access_location
        (source_tree_access_at tree location (some anchor) .Write protections .SkipChildrenOfAccessed ⟨0,capacity⟩)))},.Released⟩ := by
  unfold BorrowTree.releaseProtector
  simp only [tagged,Id.run,bind,pure,locations,show (homogeneous capacity location).entries.size=1 from rfl,Array.size_singleton]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    show List.range' 0 1=[0] from rfl,List.forIn_cons,List.forIn_nil,bind,pure]
  simp only [locations]
  rw [index_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [show (homogeneous capacity location).entries[0]'(by change 0<1;decide) = ⟨⟨0,capacity⟩,location⟩ from rfl,stored,GeneralBorrowWildcardLeaf.unique,Permission.associatedAccess,↓reduceIte,bind,pure]
  simp only [setAtPos_success (homogeneous capacity location) 0 (by change 0<1;decide)]
  simp only [callback,bind,pure]
  rw [setAtPos_exact (homogeneous capacity location) 0 (by change 0<1;decide)]
  have replacement (next : LocationTree) : replaced (homogeneous capacity location) 0 (by change 0<1;decide) next=homogeneous capacity next := by rfl
  rw [replacement]
  let next := source_access_location (source_tree_access_at tree location (some anchor) .Write protections .SkipChildrenOfAccessed ⟨0,capacity⟩)
  have taggedNext : ({tree with locations:=homogeneous capacity next}:BorrowTree).indexOfTag tag=some anchor := tagged
  have presentNext : ({tree with locations:=homogeneous capacity next}:BorrowTree).nodeAt anchor=some node := present
  dsimp only [next] at taggedNext presentNext
  unfold BorrowTree.updateExposureForProtectorRelease
  simp only [taggedNext,presentNext,hidden,Bool.not_false,↓reduceIte,Id.run,pure]
end DuplicatePrefix.GeneralBorrowHomogeneousHiddenUniqueRelease
