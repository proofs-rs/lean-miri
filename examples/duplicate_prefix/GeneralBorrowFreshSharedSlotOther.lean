import duplicate_prefix.GeneralBorrowFreshMetadataChildOld

namespace DuplicatePrefix.GeneralBorrowFreshSharedSlotOther
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshAnchor (sharedNode)
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
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (oldNode : TreeNode) (present : tree.nodeAt query = some oldNode) (notParent : query ≠ parent) :
    ∃ next, (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.parent = oldNode.parent ∧ next.children = oldNode.children ∧
      next.defaultInitialPermission = oldNode.defaultInitialPermission ∧ next.isExposed = oldNode.isExposed := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    have notNew : query ≠ GeneralBorrowFreshMetadataChildShared.index input := by
      intro same
      have valid := (GeneralBorrowProjection.array_of_node tree query oldNode present).1
      have atEnd : (GeneralBorrowFreshMetadataChildShared.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
      rw [same,atEnd] at valid
      omega
    have oldLookup := GeneralBorrowFreshGraph.other_lookup tree (GeneralBorrowFreshMetadataChildShared.index input)
      parent query parentNode (sharedNode newTag parent) (GeneralBorrowFreshMetadataChildShared.at_end input) parentPresent notParent notNew
    have stagedLookup : (GeneralBorrowFreshMetadataChildShared.stage input).nodeAt query = some oldNode := by
      simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using oldLookup.trans present
    exact transfer _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
      (GeneralBorrowFreshMetadataChildShared.exposure input) query oldNode stagedLookup
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    have notNew : query ≠ index := by
      intro same
      change tree.nodes.get query = some oldNode at present
      rw [same,vacant] at present
      cases present
    have oldLookup := GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode (sharedNode newTag parent)
      vacant parentPresent notParent notNew
    have stagedLookup : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodeAt query = some oldNode := by
      simpa only [input,GeneralBorrowFreshMetadataChildSharedReuse.index,GeneralBorrowFreshMetadataChildSharedReuse.stage,
        GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using oldLookup.trans present
    exact transfer _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
      (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) query oldNode stagedLookup

end DuplicatePrefix.GeneralBorrowFreshSharedSlotOther
