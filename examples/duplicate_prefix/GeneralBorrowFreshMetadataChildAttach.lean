import duplicate_prefix.GeneralBorrowFreshMetadataChildSifa
import duplicate_prefix.GeneralBorrowFreshProjection
import duplicate_prefix.GeneralBorrowFreshOwnership

namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildAttach
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowGraph DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshNode DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Only the graph certificates needed by subsequent actual accesses. -/
structure Certificates (tree : BorrowTree) where
  depth : ParentDepth tree.nodes
  children : ChildNodes tree
  covered : RootsCover tree

def staged (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree :=
  {(GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) with
    tagMapping := mapping,locations := locations}

set_option maxHeartbeats 1500000 in
/-- Transfer append-stage graph certificates through the real SIFA update.
The new-node policy and both mapping/range updates are arbitrary, so the same
bridge applies to shared and mutable constructors. -/
def append (tree : BorrowTree) (depth : ParentDepth tree.nodes)
    (children : ChildNodes tree) (covered : RootsCover tree)
    (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (after : BorrowTree)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations)) :
    Certificates after := by
  let stage := staged tree index parent parentNode newNode mapping locations
  have stageDepth : ParentDepth stage.nodes := by
    dsimp only [stage,staged,GeneralBorrowFreshGraph.attached]
    exact attached_depth tree.nodes depth index parent parentNode newNode atEnd parentPresent childParent
  have stageChildren : ChildNodes stage := by
    simpa only [ChildNodes,stage,staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using GeneralBorrowFreshGraph.child_nodes tree index parent parentNode newNode atEnd parentPresent leaf children
  have stageCovered : RootsCover stage := by
    simpa only [RootsCover,stage,staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using GeneralBorrowFreshGraph.roots_cover tree index parent parentNode newNode atEnd parentPresent childParent covered
  exact ⟨GeneralBorrowFreshMetadata.parent_depth stage _ same stageDepth,
    GeneralBorrowFreshMetadata.child_nodes stage _ same stageChildren,
    GeneralBorrowFreshMetadata.roots_cover stage _ same stageCovered⟩

theorem allocator (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (after : BorrowTree)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations)) :
    after.tagMapping = mapping ∧ after.roots = tree.roots ∧ after.nodes.size = tree.nodes.size+1 := by
  let stage := staged tree index parent parentNode newNode mapping locations
  have parentLookup : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (append_get_other tree.nodes index parent newNode atEnd (parent_not_fresh tree.nodes index parent parentNode atEnd parentPresent)).trans parentPresent
  refine ⟨?_,?_,?_⟩
  · simpa only [stage,staged] using GeneralBorrowFreshMetadata.mapping stage after same
  · simpa only [stage,staged,GeneralBorrowFreshGraph.attached] using GeneralBorrowFreshMetadata.roots stage after same
  ·
    calc
      after.nodes.size = stage.nodes.size :=
        GeneralBorrowFreshMetadata.node_size stage _ same
      _ = tree.nodes.size+1 := by
        dsimp only [stage,staged,GeneralBorrowFreshGraph.attached,attachedNodes]
        rw [insert_existing_size (tree.nodes.insert index newNode) parent parentNode _ parentLookup,append_size tree.nodes index newNode atEnd]

theorem new_node (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (after : BorrowTree)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after =
      GeneralBorrowFreshMetadataChildSifa.exposureShape (staged tree index parent parentNode newNode mapping locations)) :
    ∃ next, after.nodeAt index = some next ∧
      next.tag = newNode.tag ∧ next.parent = newNode.parent ∧ next.children = newNode.children ∧
      next.defaultInitialPermission = newNode.defaultInitialPermission ∧ next.isExposed = newNode.isExposed := by
  have present : (staged tree index parent parentNode newNode mapping locations).nodeAt index = some newNode := by
    simpa only [staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using GeneralBorrowFreshGraph.new_lookup tree index parent parentNode newNode atEnd parentPresent
  obtain ⟨next,lookup,tag,parentEq,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields _ after same index newNode present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure _ after exposure index
  change (staged tree index parent parentNode newNode mapping locations).nodes.get index = some newNode at present
  rw [lookup,present] at flags
  exact ⟨next,lookup,tag,parentEq,children,permission,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

/-- The projected topology is the actual leaf extension even after the real
range installation and SIFA loop, for any comparison locations/protections. -/
theorem topology_extension (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (childParent : newNode.parent = some parent) (leaf : newNode.children = #[])
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (after : BorrowTree)
    (same : treeShape after = treeShape (staged tree index parent parentNode newNode mapping locations))
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags) :
    GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation protections).topology
      (source_normal_projection after newLocation protections).topology
      parent.toNat := by
  let stage := staged tree index parent parentNode newNode mapping locations
  have projected := GeneralBorrowFreshOwnership.projection_shape stage after newLocation newLocation protections
    (GeneralBorrowFreshMetadata.node_array stage _ same) rfl
  have topology := congrArg Prod.fst projected
  change (source_normal_projection after newLocation protections).topology =
    (source_normal_projection stage newLocation protections).topology at topology
  rw [topology]
  change GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation protections).topology
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).topology parent.toNat
  exact GeneralBorrowFreshProjection.topology_extension tree index parent parentNode newNode atEnd parentPresent childParent leaf
    oldLocation newLocation protections

end DuplicatePrefix.GeneralBorrowFreshMetadataChildAttach
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildAttach." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fresh attached metadata dependency {dependency}"
