import duplicate_prefix.GeneralBorrowExposureLevelTransition
namespace DuplicatePrefix.GeneralBorrowExposurePermissionUpdate
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowExposureLevelUpdate DuplicatePrefix.GeneralBorrowExposureLevelTransition
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Effective-level functions need agree only at actual present source nodes. -/
theorem cardinality_congr (nodes : UniValMap TreeNode)
    (before after : UniIndex → TreeNode → WildcardAccessLevel)
    (same : ∀ index node,nodes.get index = some node → before index node = after index node)
    (query : UniIndex) (kind : AccessKind) : cardinality nodes before query kind = cardinality nodes after query kind := by
  unfold cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have found := (GeneralBorrowFreshReuseProtection.entries_get nodes row.1 row.2).mp member
  simp only [contributes,same row.1 row.2 found]

def newLevel (protections : ProtectedTags) (node : TreeNode) (state : LocationState) : WildcardAccessLevel :=
  state.permission.strongestAllowedLocalAccess (protections.contains node.tag)

def cacheUpdate (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex)
    (node : TreeNode) (state : LocationState) : ExposedCacheUpdate :=
  operation location.exposedCache tree.nodes (effective location protections) index node (newLevel protections node state)

def nextLocation (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (index : UniIndex)
    (node : TreeNode) (state : LocationState) : LocationTree :=
  {perms := location.perms.insert index state,exposedCache := (cacheUpdate tree location protections index node state).cache}

/-- A single actual stored-state replacement and its conditional source cache
update preserve per-location descendant cardinality. This is a cache-component
lemma: it does not assert that an arbitrary permission transition is legal. -/
theorem preserves (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : ParentDepth tree.nodes) (coherent : LocationCoherent tree location protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) (state : LocationState) :
    (cacheUpdate tree location protections index node state).outcome = .ok () ∧
      LocationCoherent tree (nextLocation tree location protections index node state) protections := by
  have updated := GeneralBorrowExposureLevelTransition.preserves location.exposedCache tree.nodes depth
    (effective location protections) coherent index node present (newLevel protections node state)
  refine ⟨updated.1,?_⟩
  intro query kind
  change counter (operation location.exposedCache tree.nodes (effective location protections) index node (newLevel protections node state)).cache query kind =
    UInt16.ofNat (cardinality tree.nodes (effective (nextLocation tree location protections index node state) protections) query kind)
  rw [updated.2 query kind]
  apply congrArg UInt16.ofNat
  apply cardinality_congr
  intro source value found
  by_cases same : source = index
  · subst source
    have nodeEq : value = node := Option.some.inj (found.symm.trans present)
    subst value
    simp only [replace,ite_true,effective,nextLocation,GeneralBorrowFreshLocation.get_same,Option.getD_some,newLevel]
  · simp only [replace,ite_eq_right same,effective,nextLocation,GeneralBorrowFreshLocation.get_other _ _ _ _ same]
end DuplicatePrefix.GeneralBorrowExposurePermissionUpdate
