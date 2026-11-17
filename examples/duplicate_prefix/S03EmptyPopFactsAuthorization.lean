import duplicate_prefix.S03EmptyPopFactsLeaf
import duplicate_prefix.GeneralBorrowRootMembership
import duplicate_prefix.GeneralBorrowExposurePointwise
import duplicate_prefix.DuplicatePrefixBorrowAuthorization

namespace DuplicatePrefix.S03EmptyPopFactsAuthorization
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForest GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A hidden leaf has no exposed descendants in the actual parent walk. -/
theorem leaf_cardinality (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (kind : AccessKind) :
    cardinality tree.nodes (effective location protections) query kind = 0 := by
  obtain ⟨forest⟩ := graph.forest location protections
  obtain ⟨depth⟩ := graph.depth
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections query node present
  have empty : (source_normal_projection tree location protections).topology.nodes[query.toNat].children = [] := by
    have projected := projection_topology_node tree location protections query.toNat query node rfl present
    simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
    rw [projected,leaf];rfl
  have filtered : tree.nodes.entries.toList.filter (contributes tree.nodes (effective location protections) query kind) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
    by_cases walked : query ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) row.1
    · have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query row.1 row.2 found _ walked
      have desc := GeneralBorrowPhysicalRootPath.projection_desc tree location protections query row.1 path
      have equal := GeneralBorrowNodeUpdate.index_injective query row.1
        (S03EmptyPopFactsLeaf.leaf_desc _ forest query.toNat valid empty row.1.toNat desc)
      have same : row.2 = node := Option.some.inj ((equal ▸ found).symm.trans present)
      simp [contributes,same,hidden]
    · simp [contributes,List.contains_iff_mem,walked]
  simp only [cardinality,filtered,List.length_nil]


end DuplicatePrefix.S03EmptyPopFactsAuthorization
