import duplicate_prefix.GeneralBorrowSharedAuthorizationSifaDepth
import duplicate_prefix.GeneralBorrowGcAnchorOwnership
import duplicate_prefix.GeneralBorrowTerminal
import duplicate_prefix.GeneralBorrowExposedScopedNormalMetadata

namespace DuplicatePrefix.GeneralBorrowSharedCallbacksData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureAncestorFold GeneralBorrowExposureCardinality
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Both callback kinds share one support at every physical root other than
selected. The cutoff remains the selected physical root's tag. -/
def Callbacks (tree : BorrowTree) (protections : ProtectedTags) (selected : UniIndex)
    (maximum : Option BorTag) (location : LocationTree) : Prop :=
  ∀ position,(valid : position < tree.roots.size) → some selected ≠ some tree.roots[position] →
    ∃ support,Authorization tree location protections tree.roots[position] position maximum .Read support ∧
      Authorization tree location protections tree.roots[position] position maximum .Write support

/-- Allocator mapping and byte-partition storage are irrelevant to the finite
callback policy once one physical row and its node graph are fixed. -/
theorem authorization_context (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position maximum kind support) :
    Authorization {tree with tagMapping := mapping,locations := locations} location protections root position maximum kind support := by
  refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,old.witness⟩
  intro entry exit legalEntry legalExit subset query node included present retained
  exact old.queries entry exit ⟨legalEntry.distinct,legalEntry.allowed⟩ ⟨legalExit.distinct,legalExit.allowed⟩
    subset query node included present retained

theorem callbacks_context (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (selected : UniIndex) (maximum : Option BorTag) (old : Callbacks tree protections selected maximum location) :
    Callbacks {tree with tagMapping := mapping,locations := locations} protections selected maximum location := by
  intro position valid different
  obtain ⟨support,read,write⟩ := old position valid different
  exact ⟨support,authorization_context tree mapping locations location protections _ _ _ _ support read,
    authorization_context tree mapping locations location protections _ _ _ _ support write⟩

/-- S01's raw row path identifies an actual listed physical root and its real
parent walk. No selected-root membership/path premise is added externally. -/
theorem root_metadata (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (parent selected : UniIndex) (maximum : Option BorTag)
    (parentNode : TreeNode) (present : tree.nodes.get parent = some parentNode)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some parent) (some selected) maximum) :
    selected ∈ tree.roots.toList ∧ selected ∈ walk tree.nodes (tree.nodes.size+1) parent := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest location protections
  have rootPath := row.rootPath parent rfl
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections parent parentNode present
  have desc := GeneralBorrowPhysicalRootPath.selected_desc _ forest parent.toNat selected.toNat geometry.1 rootPath
  have terminal := GeneralBorrowTerminal.ancestor_terminal _ forest parent.toNat geometry.1
  have lastEq : ((source_normal_projection tree location protections).topology.ancestorPath parent.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  rw [lastEq] at terminal
  obtain ⟨selectedNode,selectedPresent⟩ := row.rootPresent selected rfl
  have parentless : selectedNode.parent = none := by
    change ((source_normal_projection tree location protections).topology.nodes[selected.toNat]?.getD ⟨none,[]⟩).parent = none at terminal
    rw [projection_topology_node tree location protections selected.toNat selected selectedNode rfl selectedPresent] at terminal
    cases edge : selectedNode.parent with
    | none => rfl
    | some before => simp only [edge,Option.map_some] at terminal;cases terminal
  refine ⟨formed.covered selected selectedNode selectedPresent parentless,?_⟩
  have physical := GeneralBorrowGcAnchorOwnership.path tree depth location tree.nodes.size parent parentNode present
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
  change (sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location protections).topology.nodes.size parent.toNat).getLast? = some selected.toNat at rootPath
  rw [size,physical] at rootPath
  obtain ⟨index,member,equal⟩ := List.mem_map.mp (List.mem_of_getLast? rootPath)
  have same := GeneralBorrowNodeUpdate.index_injective index selected equal
  simpa only [same] using member

end DuplicatePrefix.GeneralBorrowSharedCallbacksData
