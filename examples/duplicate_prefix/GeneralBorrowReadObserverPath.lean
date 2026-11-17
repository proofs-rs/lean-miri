import duplicate_prefix.GeneralBorrowSharedReadPositive
import duplicate_prefix.GeneralBorrowDirectParentGeometry
namespace DuplicatePrefix.GeneralBorrowReadObserverPath
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A real direct parent shares its child's physical root. This derives the
observer root-path fact from raw graph and source geometry, not caller history. -/
theorem edge_root (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (child parent selected : UniIndex) (node : TreeNode) (present : tree.nodeAt child = some node)
    (edge : node.parent = some parent)
    (sourcePath : ∀ location protections, ((source_normal_projection tree location protections).topology.ancestorPath child.toNat).getLast? = some selected.toNat) :
    ∀ location protections, ((source_normal_projection tree location protections).topology.ancestorPath parent.toNat).getLast? = some selected.toNat := by
  intro location protections
  obtain ⟨forest⟩ := formed.forest location protections
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have bounded : child.toNat < (source_normal_projection tree location protections).topology.nodes.size := by rw [size];exact valid
  have projectedEdge : (nodeData (source_normal_projection tree location protections).topology child.toNat).parent = some parent.toNat := by
    change ((source_normal_projection tree location protections).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = _
    rw [projection_topology_node tree location protections child.toNat child node rfl present]
    simp only [edge,Option.map_some]
  have paths := GeneralBorrowDirectParentGeometry.paths _ forest child.toNat parent.toNat bounded (by
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using projectedEdge)
  have parentNonempty : (source_normal_projection tree location protections).topology.ancestorPath parent.toNat ≠ [] :=
    GeneralBorrowTerminal.ancestors_nonempty _ _ _
  have last := sourcePath location protections
  simpa only [paths.1,List.getLast?_cons_of_ne_nil parentNonempty] using last

/-- The current shared source's Read-only Positive packet already determines
its mutable direct parent's selected physical root under ANY virtual table. -/
theorem parent (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source observer selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags source selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt source = some node) (edge : node.parent = some observer) :
    ∀ location protections, ((source_normal_projection tree location protections).topology.ancestorPath observer.toNat).getLast? = some selected.toNat := by
  have geometry := GeneralBorrowSharedReadPositive.geometry tree global.protectedTags source selected maximum offset len runtime.formed.well positive
  exact edge_root tree runtime.formed.toGraphState source observer selected node present edge geometry.path

/-- The same root-path data for an actual helper child→sharedtemporary→mutable
observer chain; neither intermediate nor future root metadata is assumed. -/
theorem two_parents (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (source temporary observer selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags source selected maximum offset len)
    (node temporaryNode : TreeNode) (present : tree.nodeAt source = some node) (edge : node.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer) :
    ∀ location protections, ((source_normal_projection tree location protections).topology.ancestorPath observer.toNat).getLast? = some selected.toNat := by
  exact edge_root tree runtime.formed.toGraphState temporary observer selected temporaryNode temporaryPresent temporaryEdge
    (parent tree global runtime source temporary selected maximum offset len positive node present edge)
end DuplicatePrefix.GeneralBorrowReadObserverPath
