import duplicate_prefix.S03EmptyPopFactsAuthorization
import duplicate_prefix.GeneralBorrowWildcardSubtreeState

namespace DuplicatePrefix.S03EmptyPopFactsCallback
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForest GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Cache updates at arbitrary exposed nodes cannot reach an unexposed leaf. -/
theorem cache_frame (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (cache : ExposedCache) (index : UniIndex) (value : TreeNode)
    (found : tree.nodeAt index = some value) (exposed : value.isExposed = true)
    (before after : WildcardAccessLevel) (kind : AccessKind) :
    counter (cache.updateExposure tree.nodes index before after).cache query kind = counter cache query kind := by
  obtain ⟨forest⟩ := graph.forest default {}
  obtain ⟨depth⟩ := graph.depth
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree default {} query node present
  have empty : (source_normal_projection tree default {}).topology.nodes[query.toNat].children = [] := by
    have projected := projection_topology_node tree default {} query.toNat query node rfl present
    simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
    rw [projected,leaf];rfl
  have outside : query ∉ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index := by
    intro member
    have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query index value found _ member
    have desc := GeneralBorrowPhysicalRootPath.projection_desc tree default {} query index path
    have equal := GeneralBorrowNodeUpdate.index_injective query index
      (S03EmptyPopFactsLeaf.leaf_desc _ forest query.toNat valid empty index.toNat desc)
    have same : node = value := Option.some.inj (present.symm.trans (equal ▸ found))
    rw [←same,hidden] at exposed
    cases exposed
  rw [GeneralBorrowExposurePointwise.update_counter cache tree.nodes depth index value found before after query kind,
    if_neg outside]

theorem foreign_state (state : LocationState) (kind : AccessKind) (held : Bool)
    (inactive : state.accessed = false) :
    (state.performAccess kind .ForeignAccess held).resultingState.accessed = false := by
  rcases state with ⟨permission,accessed,sifa⟩
  change accessed = false at inactive
  subst accessed
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases sifa <;> cases held <;> cases kind <;> rfl
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases sifa <;> cases held <;> cases kind <;> rfl

theorem recorded_state (state recorded : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (inactive : state.accessed = false) (record : state.recordNewAccess kind related = .Recorded recorded) :
    recorded.accessed = false := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record;exact inactive
  · cases record

/-- A zero local counter precludes a local wildcard classification, including
primary roots, virtual roots, and the tag-cutoff filter. -/
theorem not_local (cache : ExposedCache) (root query : UniIndex) (kind : AccessKind)
    (virtual onlyForeign : Bool) (zero : counter cache query kind = 0) :
    cache.accessRelatedness root query kind virtual onlyForeign = none ∨
      cache.accessRelatedness root query kind virtual onlyForeign = some .ForeignAccess := by
  rw [DuplicatePrefixCallbackAuthorization.classify_source]
  have zero' : GeneralBorrowWildcardRelatednessBounds.count cache query kind = 0 := by
    cases kind <;> simpa [counter,GeneralBorrowWildcardRelatednessBounds.count] using congrArg UInt16.toNat zero
  rw [zero']
  cases virtual <;> cases onlyForeign <;>
    by_cases empty : GeneralBorrowWildcardRelatednessBounds.count cache root kind = 0 <;>
    simp [DuplicatePrefixCallbackAuthorization.classify,empty]

end DuplicatePrefix.S03EmptyPopFactsCallback
