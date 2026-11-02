import duplicate_prefix.GeneralBorrowSharedCallbacksData
import duplicate_prefix.GeneralBorrowReadRowNormal

namespace DuplicatePrefix.GeneralBorrowCallbackSource
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureAncestorFold GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The callback constructor needs only physical selected-root metadata and
both callback kinds. Source normal Read/Write permissions are separate. -/
structure Source (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : Option BorTag) : Prop where
  path : ((source_normal_projection tree location protections).topology.ancestorPath parent.toNat).getLast? = some selected.toNat
  present : ∃ node,tree.nodeAt selected = some node
  cutoff : maximum = (tree.nodeAt selected).map TreeNode.tag
  callbacks : Callbacks tree protections selected maximum location

theorem of_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some parent) (some selected) maximum) :
    Source tree location protections parent selected maximum :=
  ⟨row.rootPath parent rfl,row.rootPresent selected rfl,row.cutoff,row.callbacks⟩

theorem of_read_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : Option BorTag)
    (row : GeneralBorrowReadRowNormal.ReadRow tree location protections (some parent) (some selected) maximum) :
    Source tree location protections parent selected maximum :=
  ⟨row.rootPath parent rfl,row.rootPresent selected rfl,row.cutoff,row.callbacks⟩

/-- S01's raw row path identifies an actual listed physical root and its real
parent walk. No selected-root membership/path premise is added externally. -/
theorem metadata (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (parent selected : UniIndex) (maximum : Option BorTag)
    (parentNode : TreeNode) (present : tree.nodes.get parent = some parentNode)
    (row : Source tree location protections parent selected maximum) :
    selected ∈ tree.roots.toList ∧ selected ∈ walk tree.nodes (tree.nodes.size+1) parent := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest location protections
  have rootPath := row.path
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections parent parentNode present
  have desc := GeneralBorrowPhysicalRootPath.selected_desc _ forest parent.toNat selected.toNat geometry.1 rootPath
  have terminal := GeneralBorrowTerminal.ancestor_terminal _ forest parent.toNat geometry.1
  have lastEq : ((source_normal_projection tree location protections).topology.ancestorPath parent.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  rw [lastEq] at terminal
  obtain ⟨selectedNode,selectedPresent⟩ := row.present
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

end DuplicatePrefix.GeneralBorrowCallbackSource
