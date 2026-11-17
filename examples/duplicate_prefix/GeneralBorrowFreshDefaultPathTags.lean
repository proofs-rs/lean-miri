import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
namespace DuplicatePrefix.GeneralBorrowFreshDefaultPathTags
open Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowFreshLocation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem reverse_tag (tree after : BorrowTree) (index parent query : UniIndex) (parentNode newNode node : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (same : treeShape after = treeShape (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations))
    (present : after.nodeAt query = some node) (different : query ≠ index) :
    ∃ old, tree.nodeAt query = some old ∧ node.tag = old.tag := by
  obtain ⟨staged,lookup,tagEq,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations) same.symm query node present
  dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes] at lookup
  by_cases isParent : query = parent
  · subst query
    rw [get_same] at lookup
    cases lookup
    exact ⟨parentNode,parentPresent,tagEq.symm⟩
  · rw [get_other _ parent query _ isParent,get_other _ index query _ different] at lookup
    exact ⟨staged,lookup,tagEq.symm⟩

theorem append (input : GeneralBorrowFreshMetadataChildDefault.Input) (query : UniIndex) (node : TreeNode)
    (present : (GeneralBorrowFreshMetadataChildDefault.result input).nodeAt query = some node)
    (different : query ≠ GeneralBorrowFreshMetadataChildDefault.index input) :
    ∃ old, input.tree.nodeAt query = some old ∧ node.tag = old.tag := by
  exact reverse_tag input.tree _ _ input.parent query input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) node _ _
    input.parentPresent (GeneralBorrowFreshMetadataChildDefault.shape input) present different

theorem reuse (input : GeneralBorrowFreshMetadataChildDefaultReuse.Input) (query : UniIndex) (node : TreeNode)
    (present : (GeneralBorrowFreshMetadataChildDefaultReuse.result input).nodeAt query = some node)
    (different : query ≠ input.index) :
    ∃ old, input.tree.nodeAt query = some old ∧ node.tag = old.tag := by
  exact reverse_tag input.tree _ _ input.parent query input.parentNode (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) node _ _
    input.parentPresent (GeneralBorrowFreshMetadataChildDefaultReuse.shape input) present different
theorem of_slot (tree : BorrowTree) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode)
    (present : (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).nodeAt query = some node)
    (different : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot) :
    ∃ old, tree.nodeAt query = some old ∧ node.tag = old.tag := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    exact append input query node present different
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    exact reuse input query node present different

end DuplicatePrefix.GeneralBorrowFreshDefaultPathTags
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDefaultPathTags." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable path tag dependency {dependency}"
