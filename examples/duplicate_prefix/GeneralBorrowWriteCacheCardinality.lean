import duplicate_prefix.GeneralBorrowWriteCacheFold
import duplicate_prefix.GeneralBorrowWriteCardinality
namespace DuplicatePrefix.GeneralBorrowWriteCacheCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowWriteCacheFold DuplicatePrefix.GeneralBorrowWriteCardinality
open DuplicatePrefix.GeneralBorrowFrozenWriteExposure DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual visitor positions which contribute a Frozen-leaf cache decrement. -/
def leaves (root : UniIndex) (positions : List Nat) : List UniIndex :=
  positions.filterMap fun position => match UniIndex.ofNat? position with
    | none => none
    | some index => if index = root then none else some index

theorem fold_eq (positions : List Nat) (root : UniIndex) (cache : ExposedCache) :
    positions.foldl (delta root) cache =
      (leaves root positions).foldl (fun cache leaf => dropRead (dropRead cache leaf) root) cache := by
  induction positions generalizing cache with
  | nil => rfl
  | cons position rest ih =>
    cases converted : UniIndex.ofNat? position with
    | none => simpa only [leaves,List.filterMap_cons,converted,delta,List.foldl_cons] using ih cache
    | some index =>
      by_cases same : index = root
      · simpa only [leaves,List.filterMap_cons,converted,delta,ite_eq_left same,List.foldl_cons] using ih cache
      · simpa only [leaves,List.filterMap_cons,converted,delta,ite_eq_right same,List.foldl_cons] using ih (dropRead (dropRead cache index) root)

theorem counts_perm (cache : ExposedCache) (root : UniIndex) (before after : List UniIndex)
    (good : Counts cache root before) (perm : before.Perm after) : Counts cache root after := by
  refine ⟨?_,?_,good.rootWrites,?_,good.otherWrites⟩
  · intro member;exact good.rootAbsent (perm.mem_iff.mpr member)
  · rw [good.rootReads,perm.length_eq]
  · intro query different
    rw [good.otherReads query different,perm.count_eq]

attribute [local irreducible] BorrowTree.performNormalAccessAt NormalTreeState.performAccess

/-- Real normal Write followed by exact cardinality aggregation. The event
metadata and permutation remain explicit intermediate proof obligations;
there is no operation-success or final-cache premise. -/
theorem normal_complete (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (mode : ChildrenVisitMode) (present : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location {}) root.toNat .Write)
    (metadata : ∀ event ∈ ((source_normal_projection tree location {}).performAccess root.toNat .Write mode).visited,
      Nonempty (EventMetadata tree location root mode event))
    (initialLeaves : List UniIndex) (counted : Counts location.exposedCache root initialLeaves)
    (permutation : initialLeaves.Perm (leaves root
      (((source_normal_projection tree location {}).performAccess root.toNat .Write mode).visited.map TraversalEvent.node))) :
    let result := tree.performNormalAccessAt location root .Write {} mode
    result.outcome = .ok () ∧ reads result.location.exposedCache root = 1 ∧ writes result.location.exposedCache root = 1 ∧
      ∀ query,query ≠ root → reads result.location.exposedCache query = 0 ∧ writes result.location.exposedCache query = 0 := by
  obtain ⟨exactCache,success⟩ := normal tree location root rootNode mode present parentless forest owned metadata
  rw [fold_eq] at exactCache
  have finalCounts := complete _ location.exposedCache root (counts_perm _ _ _ _ counted permutation)
  exact ⟨success,exactCache.symm ▸ finalCounts⟩
end DuplicatePrefix.GeneralBorrowWriteCacheCardinality
