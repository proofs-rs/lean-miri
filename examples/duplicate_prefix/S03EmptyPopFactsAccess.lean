import duplicate_prefix.S03EmptyPopFactsWildcard
import duplicate_prefix.GeneralBorrowCompatibleScopedNormalExposure

namespace DuplicatePrefix.S03EmptyPopFactsAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection BorrowRangeAccess GeneralBorrowExposureCardinality
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Real normal access to a distinct source keeps a zero child inactive.
The actual cache result supplies its zero local counter for later callbacks. -/
theorem normal (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags)
    (query source : UniIndex) (node sourceNode : TreeNode)
    (present : tree.nodeAt query = some node) (sourcePresent : tree.nodeAt source = some sourceNode)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ source)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections source)
    (coherent : LocationCoherent tree location protections)
    (kind : AccessKind) (mode : ChildrenVisitMode)
    (inactive : (GeneralBorrowWildcardVirtualLeaf.effective location query node).accessed = false) :
    let result := tree.performNormalAccessAt location source kind protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
    (GeneralBorrowWildcardVirtualLeaf.effective result.location query node).accessed = false ∧
    counter result.location.exposedCache query kind = 0 := by
  obtain ⟨forest⟩ := graph.forest location protections
  obtain ⟨depth⟩ := graph.depth
  have owned : GeneralBorrowCompatibleScopedNormal.Owned (source_normal_projection tree location protections)
      source.toNat kind authorization.component := by
    intro index included valid
    have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    exact authorization.permissions kind index included (by rwa [←size])
  obtain ⟨done,outcome,afterCoherent⟩ := GeneralBorrowCompatibleScopedNormalExposure.access tree location protections
    source kind mode depth graph.children sourceNode sourcePresent forest authorization.component owned coherent
  have before : S03EmptyPopFactsForeign.LocationTyped location query := by
    intro state stored
    change state.accessed = false
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using inactive
  have after := S03EmptyPopFactsLeaf.normal tree location protections query source node sourceNode present sourcePresent
    leaf different forest kind mode before
  refine ⟨done,outcome,?_,?_⟩
  · cases stored : (tree.performNormalAccessAt location source kind protections mode).location.perms.get query with
    | none => simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
    | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some,S03EmptyPopFactsForeign.Inactive] using after state stored
  · rw [afterCoherent query kind,S03EmptyPopFactsAuthorization.leaf_cardinality tree _ protections graph query node present leaf hidden kind]
    rfl

end DuplicatePrefix.S03EmptyPopFactsAccess
