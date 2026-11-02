import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildOld
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshGraph (attached updatedParent)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem transfer (before after : BorrowTree) (same : treeShape after = treeShape before)
    (exposure : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (query : UniIndex) (node : TreeNode) (present : before.nodeAt query = some node) :
    ∃ next, after.nodeAt query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,lookup,tag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after same query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after exposure query
  change before.nodes.get query = some node at present
  rw [lookup,present] at flags
  exact ⟨next,lookup,tag,by simpa only [Option.map_some,Option.some.injEq] using flags⟩

theorem attached_old (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode oldNode : TreeNode)
    (parentPresent : tree.nodeAt parent = some parentNode) (present : tree.nodeAt query = some oldNode)
    (notNew : query ≠ index)
    (parentLookup : (attached tree index parent parentNode newNode).nodeAt parent = some (updatedParent parentNode index))
    (otherLookup : query ≠ parent → (attached tree index parent parentNode newNode).nodeAt query = tree.nodeAt query) :
    ∃ staged, (attached tree index parent parentNode newNode).nodeAt query = some staged ∧
      staged.tag = oldNode.tag ∧ staged.isExposed = oldNode.isExposed := by
  by_cases equal : query = parent
  · subst query
    have oldEq : oldNode = parentNode := Option.some.inj (present.symm.trans parentPresent)
    subst oldNode
    exact ⟨_,parentLookup,rfl,rfl⟩
  · exact ⟨oldNode,(otherLookup equal).trans present,rfl,rfl⟩

theorem append (input : GeneralBorrowFreshMetadataChildShared.Input) (query : UniIndex) (oldNode : TreeNode)
    (present : input.tree.nodeAt query = some oldNode) :
    ∃ next, (GeneralBorrowFreshMetadataChildShared.result input).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed := by
  let index := GeneralBorrowFreshMetadataChildShared.index input
  have atEnd := GeneralBorrowFreshMetadataChildShared.at_end input
  have different : query ≠ index := by
    intro equal
    have bounded := lookup_valid input.tree.nodes query oldNode present
    rw [equal,atEnd] at bounded
    omega
  have parentLookup := GeneralBorrowFreshGraph.parent_lookup input.tree index input.parent input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) atEnd input.parentPresent
  have otherLookup := fun notParent => GeneralBorrowFreshGraph.other_lookup input.tree index input.parent query input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) atEnd input.parentPresent notParent different
  obtain ⟨staged,lookup,tag,exposed⟩ := attached_old input.tree index input.parent query input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) oldNode input.parentPresent present different parentLookup otherLookup
  have stagedLookup : (GeneralBorrowFreshMetadataChildShared.stage input).nodeAt query = some staged := by
    simpa only [GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,attached,BorrowTree.nodeAt] using lookup
  obtain ⟨next,lookup,tagEq,exposedEq⟩ := transfer _ _ (GeneralBorrowFreshMetadataChildShared.shape input)
    (GeneralBorrowFreshMetadataChildShared.exposure input) query staged stagedLookup
  exact ⟨next,lookup,tagEq.trans tag,exposedEq.trans exposed⟩

theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (query : UniIndex) (oldNode : TreeNode)
    (present : input.tree.nodeAt query = some oldNode) :
    ∃ next, (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed := by
  let index := GeneralBorrowFreshMetadataChildSharedReuse.index input
  have different : query ≠ index := by
    intro equal
    change input.tree.nodes.get query = some oldNode at present
    have vacant : input.tree.nodes.get index = none := input.vacant
    rw [equal,vacant] at present
    cases present
  have parentLookup := GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup input.tree index input.parent input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.vacant input.parentPresent
  have otherLookup := fun notParent => GeneralBorrowFreshMetadataChildReuseGraph.other_lookup input.tree index input.parent query input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) input.vacant input.parentPresent notParent different
  obtain ⟨staged,lookup,tag,exposed⟩ := attached_old input.tree index input.parent query input.parentNode
    (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) oldNode input.parentPresent present different parentLookup otherLookup
  have stagedLookup : (GeneralBorrowFreshMetadataChildSharedReuse.stage input).nodeAt query = some staged := by
    simpa only [GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,attached,BorrowTree.nodeAt] using lookup
  obtain ⟨next,lookup,tagEq,exposedEq⟩ := transfer _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input)
    (GeneralBorrowFreshMetadataChildSharedReuse.exposure input) query staged stagedLookup
  exact ⟨next,lookup,tagEq.trans tag,exposedEq.trans exposed⟩
theorem of_slot (tree : BorrowTree) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (oldNode : TreeNode) (present : tree.nodeAt query = some oldNode) :
    ∃ next, (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len).nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    exact append input query oldNode present
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    exact reuse input query oldNode present

end DuplicatePrefix.GeneralBorrowFreshMetadataChildOld
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildOld." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved old-node metadata dependency {dependency}"
