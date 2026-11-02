import duplicate_prefix.GeneralBorrowGcFullClean
import duplicate_prefix.GeneralBorrowSharedGeneratorProfile

namespace DuplicatePrefix.GeneralBorrowGcPermissionPolicy
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowGcVacantClean
open DuplicatePrefix.GeneralBorrowGcRangeClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- A fixed per-index permission policy for surviving nodes, together with
absence of stale permissions at every vacant sparse slot. Unlike a generator
Profile this does not assert that a distinguished root survives deletion. -/
structure Policy (expected : UniIndex → LocationState) (tree : BorrowTree) : Prop where
  live : ∀ query node, tree.nodes.get query = some node →
    Every (fun location => location.perms.get query = some (expected query)) tree.locations
  vacant : VacantClean tree

/-- Actual GC node deletion removes that index's permissions and preserves
all other live permissions. Missing-node errors retain the input policy. -/
theorem remove_preserves (expected : UniIndex → LocationState) (tree : BorrowTree)
    (index : UniIndex) (good : Policy expected tree) :
    Policy expected (source_remove_useless_node tree index).1 := by
  refine ⟨?_,GeneralBorrowGcVacantClean.remove_preserves tree index good.vacant⟩
  cases stored : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,bind,pure] using good.live
  | some removed =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    intro query node present position valid
    change (tree.nodes.remove index).get query = some node at present
    have different : query ≠ index := by
      intro equal
      subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    rw [GeneralBorrowSparseRemoval.remove_get_other _ index query different] at present
    have previous : position < tree.locations.entries.size := by
      simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
    have known := good.live query node present position previous
    simpa only [DedupRangeMap.modifyAll,Array.getElem_map,
      GeneralBorrowSparseRemoval.remove_get_other _ index query different] using known

/-- Existing-node metadata updates change neither the policy's live domain nor
its stored permissions. No parent-link or child-list equality is required. -/
theorem update_preserves (expected : UniIndex → LocationState) (tree : BorrowTree)
    (index : UniIndex) (oldNode newNode : TreeNode)
    (present : tree.nodes.get index = some oldNode) (good : Policy expected tree) :
    Policy expected {tree with nodes := tree.nodes.insert index newNode} := by
  refine ⟨?_,insert_preserves tree index newNode good.vacant⟩
  intro query node found
  change (tree.nodes.insert index newNode).get query = some node at found
  by_cases same : query = index
  · subst query
    exact good.live index oldNode present
  · rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ index query oldNode newNode present same] at found
    exact good.live query node found

/-- Actual trailing-None normalization preserves the policy by lookup equality. -/
theorem trim_preserves (expected : UniIndex → LocationState) (tree : BorrowTree)
    (good : Policy expected tree) :
    Policy expected {tree with locations := tree.locations.modifyAll (fun _ location => gc_source_trim_location location)} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.trim_preserves tree good.vacant⟩
  intro query node present position valid
  have previous : position < tree.locations.entries.size := by
    simpa only [DedupRangeMap.modifyAll,Array.size_map] using valid
  have known := good.live query node present position previous
  simpa only [DedupRangeMap.modifyAll,Array.getElem_map,trim_location_get] using known

/-- Thorough range merging preserves every surviving node's exact permission,
including partial states on range-merge errors. -/
theorem merge_preserves (expected : UniIndex → LocationState) (tree : BorrowTree)
    (good : Policy expected tree) :
    Policy expected {tree with locations := tree.locations.mergeAdjacentThorough.state} := by
  refine ⟨?_,GeneralBorrowGcRangeClean.merge_preserves tree good.vacant⟩
  intro query node present
  exact GeneralRangeMapThoroughEvery.preserves
    (fun location : LocationTree => location.perms.get query = some (expected query))
    tree.locations (good.live query node present)

/-- The full production GC preserves exact live permissions and vacant Clean
through its actual postorder walker, node removal, metadata rewrites,
normalization and range merging. This includes error outputs as data states;
it does not establish GC completion, graph validity or whole-call safety. -/
theorem preserves (expected : UniIndex → LocationState) (tree : BorrowTree)
    (liveTags : Array BorTag) (good : Policy expected tree) :
    Policy expected (tree.removeUnreachableTags liveTags).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Policy expected) tree liveTags good
  · intro current root initial
    exact GeneralBorrowGcWhileInvariant.preserves (Policy expected)
      (fun current index initial => remove_preserves expected current index initial)
      (fun current index oldNode newNode present _ initial =>
        update_preserves expected current index oldNode newNode present initial)
      current root liveTags initial
  · intro current initial
    exact merge_preserves expected _ (trim_preserves expected current initial)

end DuplicatePrefix.GeneralBorrowGcPermissionPolicy
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGcPermissionPolicy.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved GC permission policy dependency {dependency}"
