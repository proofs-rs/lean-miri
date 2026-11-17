import duplicate_prefix.GeneralBorrowGcPermissionPolicy
import duplicate_prefix.GeneralBorrowGcLeafProperty
import duplicate_prefix.GeneralBorrowGcStarShape

namespace DuplicatePrefix.GeneralBorrowGcEffectivePolicy
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowGcVacantClean DuplicatePrefix.GeneralBorrowGcRangeClean
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- Effective permission constraints may differ by interval and include lazy
states. Absence of stored permissions at vacant slots is a separate invariant. -/
structure Policy (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) : Prop where
  live : ∀ query node, tree.nodes.get query = some node →
    Every (fun location => allowed query ((location.perms.get query).getD node.defaultLocationState)) tree.locations
  vacant : VacantClean tree

theorem remove (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree)
    (index : UniIndex) (good : Policy allowed tree) : Policy allowed (source_remove_useless_node tree index).1 := by
  refine ⟨?_,GeneralBorrowGcVacantClean.remove_preserves tree index good.vacant⟩
  cases stored : tree.nodes.get index with
  | none => unfold_source_remove_useless_node;simpa only [stored,Id.run,bind,pure] using good.live
  | some removed =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    intro query node present position valid
    change (tree.nodes.remove index).get query = some node at present
    have different : query ≠ index := by
      intro same;subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at present
    have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,GeneralBorrowSparseRemoval.remove_get_other _ index query different] using good.live query node present position previous

theorem update (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) (index : UniIndex)
    (oldNode newNode : TreeNode) (present : tree.nodes.get index = some oldNode)
    (defaults : newNode.defaultLocationState = oldNode.defaultLocationState) (good : Policy allowed tree) :
    Policy allowed {tree with nodes := tree.nodes.insert index newNode} := by
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

theorem trim (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) (good : Policy allowed tree) :
    Policy allowed {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.trim_preserves tree good.vacant⟩
  intro query node present position valid
  have previous : position < tree.locations.entries.size := by simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  simpa only [DedupRangeMap.modifyAll,Array.getElem_map,trim_location_get] using good.live query node present position previous

theorem merge (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) (good : Policy allowed tree) :
    Policy allowed {tree with locations := tree.locations.mergeAdjacentThorough.state} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.merge_preserves tree good.vacant⟩
  intro query node present
  exact GeneralRangeMapThoroughEvery.preserves _ tree.locations (good.live query node present)

/-- A real star GC only removes leaves and changes the root's child list. -/
theorem children (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (live : Array BorTag) (star : GeneralBorrowGeneratedStarShape.Star tree root node) (good : Policy allowed tree) :
    Policy allowed (source_gc_children tree root live).tree := by
  have notChild : root ∉ node.children.toList := fun member => ((star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  obtain ⟨after,kept,walked,rootPresent,capacity,folded⟩ := GeneralBorrowGcStarWalk.complete tree root node live
    star.present star.distinct notChild leaves (GeneralBorrowGeneratedStarShape.children_bound tree root node star)
  obtain ⟨other,result,done,_,_,policy⟩ := GeneralBorrowGcLeafProperty.complete (Policy allowed)
    (fun current index initial => remove allowed current index initial)
    node.children.toList tree tree root root live #[] star.distinct leaves good
  have same := congrArg (fun row : Option BorrowTree.TreeGcResult × BorrowTree × Array UniIndex => row.2.1) (folded.symm.trans done)
  change after = other at same
  subst other
  rw [walked]
  exact update allowed after root node {node with children := kept} rootPresent rfl policy

/-- Full production GC retains effective permission constraints across actual
leaf deletions, normalization and merging. Errors are only data preservation. -/
theorem preserves (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (live : Array BorTag) (star : GeneralBorrowGeneratedStarShape.Star tree root node) (roots : tree.roots = #[root])
    (good : Policy allowed tree) : Policy allowed (tree.removeUnreachableTags live).tree := by
  have walked := children allowed tree root node live star good
  have notChild : root ∉ node.children.toList := fun member => ((star.children root).mp member).1 rfl
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (star.children index).mp member
    exact ⟨child,present,(star.leaves index child present different).2⟩
  obtain ⟨after,kept,exactWalk,_,_,_⟩ := GeneralBorrowGcStarWalk.complete tree root node live
    star.present star.distinct notChild leaves (GeneralBorrowGeneratedStarShape.children_bound tree root node star)
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [exactWalk]
  have finished := merge allowed _ (trim allowed _ walked)
  unfold BorrowTree.removeUnreachableTags
  rw [roots]
  simp only [Id.run,bind,pure,←Array.forIn_toList,show (#[root] : Array UniIndex).toList = [root] from rfl,
    List.forIn_cons,List.forIn_nil]
  rw [show (gc_root_children tree root live).outcome = .ok () from success]
  simp only [bind,pure]
  split <;> exact finished

end DuplicatePrefix.GeneralBorrowGcEffectivePolicy
