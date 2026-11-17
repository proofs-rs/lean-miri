import duplicate_prefix.GeneralBorrowFreshGraph
import duplicate_prefix.GeneralBorrowFreshTopology
import duplicate_prefix.GeneralBorrowFreshLocation
namespace DuplicatePrefix.GeneralBorrowFreshProjection
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- The actual two node insertions project to the pure fresh-child extension.
Location data and protector values do not enter this topology equation. -/
theorem topology_exact (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology =
      GeneralBorrowFreshTopology.attached (source_normal_projection tree oldLocation protections).topology parent.toNat
        (by
          have valid := lookup_valid tree.nodes parent parentNode parentPresent
          unfold_general_projection
          unfold_general_topology
          simpa only [Array.size_map] using valid) := by
  have parentValid := lookup_valid tree.nodes parent parentNode parentPresent
  have parentSlot : tree.nodes.data[parent.toNat]'parentValid = some parentNode := by
    simpa only [BorrowTree.nodeAt,UniValMap.get,Array.getElem?_eq_getElem parentValid] using parentPresent
  have firstLookup : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd
      (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  have secondData := insert_existing (tree.nodes.insert index newNode) parent parentNode
    {parentNode with children := parentNode.children.push index} firstLookup
  unfold_general_projection
  unfold_general_topology
  dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes]
  simp only [secondData,insert_append tree.nodes index newNode atEnd]
  simp only [GeneralBorrowFreshTopology.attached,Array.map_set,Array.map_push,Array.getElem_map,
    parentSlot,childParent,leaf,Option.map_some,Array.toList_empty,List.map_nil,
    Array.toList_push,List.map_append,List.map_singleton,atEnd,Array.size_map]

/-- A certificate for the actual projected fresh-child shape, ready for
forest and ancestor-path transport. -/
theorem topology_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology parent.toNat := by
  rw [topology_exact tree index parent parentNode newNode atEnd parentPresent childParent leaf oldLocation newLocation protections]
  exact GeneralBorrowFreshTopology.attached_extension _ _ _

/-- The full forest certificate for the real projected child topology is
constructed from the old arbitrary allocation forest. -/
def projected_forest (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    GeneralBorrowForest.Forest
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology :=
  GeneralBorrowFreshTopology.extended_forest _ _ _
    (topology_extension tree index parent parentNode newNode atEnd parentPresent childParent leaf oldLocation newLocation protections) forest

/-- The actual new index and its ancestors are precisely the new child followed
by the old parent's ancestors. No fixed number of caller-history nodes occurs. -/
theorem projected_ancestors (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology.ancestorPath index.toNat =
      index.toNat :: (source_normal_projection tree oldLocation protections).topology.ancestorPath parent.toNat := by
  have size : (source_normal_projection tree oldLocation protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have path := GeneralBorrowFreshTopology.ancestors_new _ _ _
    (topology_extension tree index parent parentNode newNode atEnd parentPresent childParent leaf oldLocation newLocation protections) forest
  rw [size,←atEnd] at path
  exact path

end DuplicatePrefix.GeneralBorrowFreshProjection
#print axioms DuplicatePrefix.GeneralBorrowFreshProjection.topology_extension
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshProjection." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh projection dependency {dependency}"
