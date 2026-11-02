import duplicate_prefix.GeneralBorrowGcPermissionPolicy
import duplicate_prefix.GeneralBorrowGcLeafProperty
import duplicate_prefix.GeneralBorrowGcDefaultWhile
import duplicate_prefix.GeneralRangeMapThoroughOwnedOn

namespace DuplicatePrefix.GeneralBorrowGcLocalEffectivePolicy
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowGcVacantClean DuplicatePrefix.GeneralBorrowGcRangeClean
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Effective permission constraints may differ by interval and include lazy
states. Absence of stored permissions at vacant slots is a separate invariant. -/
structure Policy (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64) (tree : BorrowTree) : Prop where
  live : ∀ query node, tree.nodes.get query = some node →
    OwnedOn (fun location => allowed query ((location.perms.get query).getD node.defaultLocationState)) lower upper tree.locations
  vacant : VacantClean tree

theorem remove (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64) (tree : BorrowTree)
    (index : UniIndex) (good : Policy allowed lower upper tree) : Policy allowed lower upper (source_remove_useless_node tree index).1 := by
  refine ⟨?_,GeneralBorrowGcVacantClean.remove_preserves tree index good.vacant⟩
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,bind,pure] using good.live
  | some removed =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    intro query node present position valid positive beforeUpper afterLower
    change (tree.nodes.remove index).get query = some node at present
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at present
    have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,GeneralBorrowSparseRemoval.remove_get_other _ index query different] using good.live query node present position previous positive
      (by simpa only [DedupRangeMap.modifyAll,Array.getElem_map] using beforeUpper)
      (by simpa only [DedupRangeMap.modifyAll,Array.getElem_map] using afterLower)

theorem update (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64) (tree : BorrowTree) (index : UniIndex)
    (oldNode newNode : TreeNode) (present : tree.nodes.get index = some oldNode)
    (defaults : newNode.defaultLocationState = oldNode.defaultLocationState) (good : Policy allowed lower upper tree) :
    Policy allowed lower upper {tree with nodes := tree.nodes.insert index newNode} := by
  refine ⟨?_,GeneralBorrowGcVacantClean.insert_preserves tree index newNode good.vacant⟩
  intro query node found
  change (tree.nodes.insert index newNode).get query = some node at found
  by_cases same : query = index
  · subst query
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    simpa only [defaults] using good.live index oldNode present
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ index query oldNode newNode present same] at found
    exact good.live query node found

theorem trim (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64) (tree : BorrowTree) (good : Policy allowed lower upper tree) :
    Policy allowed lower upper {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.trim_preserves tree good.vacant⟩
  intro query node present position valid positive beforeUpper afterLower
  have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  simpa only [DedupRangeMap.modifyAll,Array.getElem_map,trim_location_get] using good.live query node present position previous positive
      (by simpa only [DedupRangeMap.modifyAll,Array.getElem_map] using beforeUpper)
      (by simpa only [DedupRangeMap.modifyAll,Array.getElem_map] using afterLower)

theorem merge (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64) (tree : BorrowTree) (good : Policy allowed lower upper tree) :
    Policy allowed lower upper {tree with locations := tree.locations.mergeAdjacentThorough.state} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.merge_preserves tree good.vacant⟩
  intro query node present
  exact GeneralRangeMapThoroughOwnedOn.preserves _ lower upper tree.locations (good.live query node present)

/-- Range-local effective permission policies survive arbitrary-tree fullGC,
including actual trim/merge and every error prefix. -/
theorem preserves (allowed : UniIndex → LocationState → Prop) (lower upper : UInt64)
    (tree : BorrowTree) (live : Array BorTag) (good : Policy allowed lower upper tree) :
    Policy allowed lower upper (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Policy allowed lower upper) tree live good
  · intro current root initial
    exact GeneralBorrowGcDefaultWhile.preserves (Policy allowed lower upper)
      (remove allowed lower upper) (update allowed lower upper) current root live initial
  · intro current initial
    exact merge allowed lower upper _ (trim allowed lower upper _ initial)
end DuplicatePrefix.GeneralBorrowGcLocalEffectivePolicy
