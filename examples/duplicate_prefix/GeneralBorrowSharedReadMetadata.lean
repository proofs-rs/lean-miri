import duplicate_prefix.GeneralBorrowSharedReadConstructor
namespace DuplicatePrefix.GeneralBorrowSharedReadMetadata
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshNode GeneralBorrowNodeUpdate GeneralBorrowFreshAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local irreducible] UniValMap.insert

structure Data (before after : BorrowTree) (parent child : UniIndex) : Prop where
  paths : ∀ oldLocation newLocation protections,
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection before oldLocation protections).topology
      (source_normal_projection after newLocation protections).topology parent.toNat child.toNat
  nodes : ∀ query node, before.nodes.get query = some node →
    ∃ next, after.nodes.get query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed
  roots : after.roots = before.roots
  childPresent : ∃ node, after.nodeAt child = some node

private theorem attached_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (present : tree.nodes.get parent = some parentNode) :
    ∀ query node, tree.nodes.get query = some node →
    ∃ next, (attachedNodes tree.nodes index parent parentNode newNode).get query = some next ∧
      next.tag = node.tag ∧ next.isExposed = node.isExposed := by
  intro query node found
  have parentDifferent : parent ≠ index := by intro same;rw [same,vacant] at present;cases present
  have parentAfter : (tree.nodes.insert index newNode).get parent = some parentNode :=
    (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode parentDifferent).trans present
  have queryDifferent : query ≠ index := by intro same;rw [same,vacant] at found;cases found
  by_cases isParent : query = parent
  · subst query
    have same := Option.some.inj (found.symm.trans present)
    subst node
    exact ⟨{parentNode with children := parentNode.children.push index},
      insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ parentAfter,rfl,rfl⟩
  · refine ⟨node,?_,rfl,rfl⟩
    unfold attachedNodes
    rw [GeneralBorrowFreshLocation.get_other _ parent query _ isParent,
      GeneralBorrowFreshLocation.get_other _ index query _ queryDifferent,found]

private theorem old_nodes (tree after : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : tree.nodes.get index = none) (present : tree.nodes.get parent = some parentNode)
    (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape
      (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape
      (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations)) :
    ∀ query node, tree.nodes.get query = some node →
    ∃ next, after.nodes.get query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed := by
  intro query node found
  obtain ⟨middle,middleFound,tag,exposed⟩ := attached_old tree index parent parentNode newNode vacant present query node found
  have stagedFound : (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations).nodes.get query = some middle := middleFound
  obtain ⟨next,nextFound,nextTag,_⟩ := GeneralBorrowFreshMetadata.node_fields _ after same query middle stagedFound
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure _ after exposure query
  rw [nextFound,stagedFound] at flags
  refine ⟨next,nextFound,nextTag.trans tag,?_⟩
  have sameFlag : next.isExposed = middle.isExposed := by simpa only [Option.map_some,Option.some.injEq] using flags
  exact sameFlag.trans exposed

/-- Exact graph/path metadata for the actual shared constructor, independent
of all source permission capabilities and the fresh protector state. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    ∃ child,actual.tree.indexOfTag newTag = some child ∧ Data tree actual.tree parent child := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have output := GeneralBorrowFreshMetadataChildShared.append input
    have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildShared.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    refine ⟨GeneralBorrowFreshMetadataChildShared.index input,output.freshLookup,⟨?_,?_,output.roots,?_⟩⟩
    · intro oldLocation newLocation protections
      obtain ⟨forest⟩ := runtime.formed.toGraphState.forest oldLocation protections
      have extension := output.extension oldLocation newLocation protections
      have paths := GeneralBorrowFreshSharedPaths.of_append _ _ parent.toNat extension forest
      have size : (source_normal_projection tree oldLocation protections).topology.nodes.size = tree.nodes.data.size := by
        unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
      rw [size,←atEnd] at paths
      exact paths
    · exact old_nodes tree _ _ parent parentNode (sharedNode newTag parent) _ _ vacant present
        (GeneralBorrowFreshMetadataChildShared.shape input) (GeneralBorrowFreshMetadataChildShared.exposure input)
    · obtain ⟨node,present,_⟩ := output.newNode
      exact ⟨node,present⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    have output := GeneralBorrowFreshMetadataChildSharedReuse.reuse input
    refine ⟨index,output.freshLookup,⟨?_,?_,output.roots,?_⟩⟩
    · intro oldLocation newLocation protections
      obtain ⟨forest⟩ := runtime.formed.toGraphState.forest oldLocation protections
      exact GeneralBorrowFreshSharedPaths.of_reuse _ _ index.toNat parent.toNat
        (output.extension oldLocation newLocation protections) forest
    · exact old_nodes tree _ index parent parentNode (sharedNode newTag parent) _ _ vacant present
        (GeneralBorrowFreshMetadataChildSharedReuse.shape input) (GeneralBorrowFreshMetadataChildSharedReuse.exposure input)
    · obtain ⟨node,present,_⟩ := output.newNode
      exact ⟨node,present⟩
end DuplicatePrefix.GeneralBorrowSharedReadMetadata
