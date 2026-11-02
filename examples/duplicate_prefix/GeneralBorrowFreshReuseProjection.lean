import duplicate_prefix.GeneralBorrowFreshGraph
import duplicate_prefix.GeneralBorrowFreshReuseTopology
import duplicate_prefix.GeneralBorrowFreshReuseNode
import duplicate_prefix.GeneralBorrowFreshLocation
namespace DuplicatePrefix.GeneralBorrowFreshReuseProjection
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

/-- The actual two node insertions project to the pure vacant-slot replacement.
Location data and protector values do not enter this topology equation. -/
theorem topology_exact (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology =
      GeneralBorrowFreshReuseTopology.attached (source_normal_projection tree oldLocation protections).topology index.toNat parent.toNat
        (by unfold_general_projection;unfold_general_topology;simpa only [Array.size_map] using valid)
        (by
          have valid := lookup_valid tree.nodes parent parentNode parentPresent
          unfold_general_projection
          unfold_general_topology
          simpa only [Array.size_map] using valid) := by
  have parentValid := lookup_valid tree.nodes parent parentNode parentPresent
  have parentSlot : tree.nodes.data[parent.toNat]'parentValid = some parentNode := by
    simpa only [BorrowTree.nodeAt,UniValMap.get,Array.getElem?_eq_getElem parentValid] using parentPresent
  have firstLookup : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
      (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  have secondData := insert_existing (tree.nodes.insert index newNode) parent parentNode
    {parentNode with children := parentNode.children.push index} firstLookup
  unfold_general_projection
  unfold_general_topology
  dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes]
  simp only [secondData,GeneralBorrowFreshReuseNode.insert_bounded tree.nodes index newNode valid]
  simp only [GeneralBorrowFreshReuseTopology.attached,Array.map_set,Array.getElem_map,
    parentSlot,childParent,leaf,Option.map_some,Array.toList_empty,List.map_nil,
    Array.toList_push,List.map_append,List.map_singleton,Array.size_map]

/-- A certificate for the actual projected reused-child shape, ready for
forest and ancestor-path transport. -/
theorem topology_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    GeneralBorrowFreshReuseTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology index.toNat parent.toNat := by
  rw [topology_exact tree index parent parentNode newNode valid vacant parentPresent childParent leaf oldLocation newLocation protections]
  have different : parent.toNat ≠ index.toNat := by
    intro equal
    exact GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent
      (index_injective parent index equal)
  have slot : tree.nodes.data[index.toNat]'valid = none := by
    simpa only [UniValMap.get,Array.getElem?_eq_getElem valid] using vacant
  apply GeneralBorrowFreshReuseTopology.attached_extension _ _ _ _ _ different
  unfold_general_projection
  unfold_general_topology
  simp only [Array.getElem_map,slot]

/-- The full forest certificate for the real projected child topology is
constructed from the old arbitrary allocation forest. -/
def projected_forest (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    GeneralBorrowForest.Forest
      (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology :=
  GeneralBorrowFreshReuseTopology.extended_forest _ _ _ _
    (topology_extension tree index parent parentNode newNode valid vacant parentPresent childParent leaf oldLocation newLocation protections) forest

/-- The actual new index and its ancestors are precisely the new child followed
by the old parent's ancestors. No fixed number of caller-history nodes occurs. -/
theorem projected_ancestors (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (valid : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation protections).topology) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology.ancestorPath index.toNat =
      index.toNat :: (source_normal_projection tree oldLocation protections).topology.ancestorPath parent.toNat := by
  exact GeneralBorrowFreshReuseTopology.ancestors_new _ _ _ _
    (topology_extension tree index parent parentNode newNode valid vacant parentPresent childParent leaf oldLocation newLocation protections) forest

end DuplicatePrefix.GeneralBorrowFreshReuseProjection
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseProjection.topology_extension
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseProjection." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh projection dependency {dependency}"
