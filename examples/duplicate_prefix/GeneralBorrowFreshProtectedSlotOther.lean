import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GeneralBorrowFreshProtectedSlotOther
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshChild (child)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The real SIFA poststate preserves every structural field of any staged node,
plus its exposure flag. This does not assume its permission-operation outcome. -/
theorem transfer (before after : BorrowTree) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (query : UniIndex) (node : TreeNode) (present : before.nodeAt query = some node) :
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.children = node.children ∧ next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,lookup,tag,parent,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields before after same query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after exposure query
  change before.nodes.get query = some node at present
  rw [lookup,present] at flags
  exact ⟨next,lookup,tag,parent,children,permission,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

/-- Any existing node OTHER than the actual constructor parent retains its
full graph metadata through real append/reuse, range installation and SIFA.
Its presence internally excludes the fresh/vacant insertion slot. -/
theorem of_slot (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (oldNode : TreeNode) (present : tree.nodeAt query = some oldNode) (notParent : query ≠ parent) :
    ∃ next, (GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.children = oldNode.children ∧
      next.defaultInitialPermission = oldNode.defaultInitialPermission ∧ next.isExposed = oldNode.isExposed := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have notNew : query ≠ GeneralBorrowFreshMetadataChildMutable.index input := by
      intro same
      have valid := (GeneralBorrowProjection.array_of_node tree query oldNode present).1
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      rw [same,atEnd] at valid
      omega
    have oldLookup := GeneralBorrowFreshGraph.other_lookup tree (GeneralBorrowFreshMetadataChildMutable.index input)
      parent query parentNode (child newTag parent) (GeneralBorrowFreshMetadataChildMutable.at_end input) parentPresent notParent notNew
    have stagedLookup : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt query = some oldNode := by
      simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using oldLookup.trans present
    exact transfer _ _ (GeneralBorrowFreshMetadataChildMutable.shape input)
      (GeneralBorrowFreshMetadataChildMutable.exposure input) query oldNode stagedLookup
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have notNew : query ≠ index := by
      intro same
      change tree.nodes.get query = some oldNode at present
      rw [same,vacant] at present
      cases present
    have oldLookup := GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode (child newTag parent)
      vacant parentPresent notParent notNew
    have stagedLookup : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt query = some oldNode := by
      simpa only [input,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableReuse.stage,
        GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using oldLookup.trans present
    exact transfer _ _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input)
      (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) query oldNode stagedLookup

end DuplicatePrefix.GeneralBorrowFreshProtectedSlotOther
