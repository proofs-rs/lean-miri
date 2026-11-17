import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
import duplicate_prefix.GeneralBorrowFreshReuseProtection
namespace DuplicatePrefix.GeneralBorrowFreshMetadataChildProtector
open Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowFreshLocation
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem of_shape (before after : BorrowTree) (same : treeShape after = treeShape before) (tag : BorTag)
    (fresh : GeneralBorrowProtector.Fresh before tag) : GeneralBorrowProtector.Fresh after tag := by
  intro row member
  rcases row with ⟨query,node⟩
  have present := (GeneralBorrowFreshReuseProtection.entries_get after.nodes query node).mp (Array.mem_def.mp member)
  obtain ⟨old,lookup,tagEq,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields after before same.symm query node present
  have oldMember := (GeneralBorrowFreshReuseProtection.entries_get before.nodes query old).mpr lookup
  have different := fresh (query,old) (Array.mem_def.mpr oldMember)
  exact tagEq ▸ different

def NodeFresh (nodes : UniValMap TreeNode) (tag : BorTag) : Prop :=
  ∀ query node, nodes.get query = some node → node.tag ≠ tag

theorem node_fresh (tree : BorrowTree) (tag : BorTag) (fresh : GeneralBorrowProtector.Fresh tree tag) :
    NodeFresh tree.nodes tag := by
  intro query node lookup
  exact fresh (query,node) (Array.mem_def.mpr ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mpr lookup))

theorem fresh_of_nodes (tree : BorrowTree) (tag : BorTag) (fresh : NodeFresh tree.nodes tag) :
    GeneralBorrowProtector.Fresh tree tag := by
  intro row member
  rcases row with ⟨query,node⟩
  exact fresh query node ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mp (Array.mem_def.mp member))

theorem insert (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) (tag : BorTag)
    (fresh : NodeFresh nodes tag) (different : node.tag ≠ tag) : NodeFresh (nodes.insert index node) tag := by
  intro query next lookup
  by_cases same : query = index
  · subst query
    rw [get_same] at lookup
    cases lookup
    exact different
  · rw [get_other nodes index query node same] at lookup
    exact fresh query next lookup

theorem staged (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) (tag : BorTag)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowProtector.Fresh tree tag) (different : newNode.tag ≠ tag) :
    GeneralBorrowProtector.Fresh (GeneralBorrowFreshMetadataChildAttach.staged tree index parent parentNode newNode mapping locations) tag := by
  have original := node_fresh tree tag fresh
  have parentDifferent := original parent parentNode parentPresent
  have first := insert tree.nodes index newNode tag original different
  have second := insert (tree.nodes.insert index newNode) parent {parentNode with children := parentNode.children.push index} tag first parentDifferent
  apply fresh_of_nodes
  dsimp only [GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,GeneralBorrowFreshNode.attachedNodes]
  exact second

theorem append (input : GeneralBorrowFreshMetadataChildShared.Input) (next : BorTag)
    (fresh : GeneralBorrowProtector.Fresh input.tree next) (different : input.newTag ≠ next) :
    GeneralBorrowProtector.Fresh (GeneralBorrowFreshMetadataChildShared.result input) next := by
  apply of_shape _ _ (GeneralBorrowFreshMetadataChildShared.shape input) next
  exact staged input.tree _ input.parent input.parentNode (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    _ _ next input.parentPresent fresh different

theorem reuse (input : GeneralBorrowFreshMetadataChildSharedReuse.Input) (next : BorTag)
    (fresh : GeneralBorrowProtector.Fresh input.tree next) (different : input.newTag ≠ next) :
    GeneralBorrowProtector.Fresh (GeneralBorrowFreshMetadataChildSharedReuse.result input) next := by
  apply of_shape _ _ (GeneralBorrowFreshMetadataChildSharedReuse.shape input) next
  exact staged input.tree _ input.parent input.parentNode (DuplicatePrefix.GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)
    _ _ next input.parentPresent fresh different
theorem of_slot (tree : BorrowTree) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (next : BorTag) (protectorFresh : GeneralBorrowProtector.Fresh tree next) (different : newTag ≠ next) :
    GeneralBorrowProtector.Fresh (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len) next := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    exact append input next protectorFresh different
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    exact reuse input next protectorFresh different

end DuplicatePrefix.GeneralBorrowFreshMetadataChildProtector
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadataChildProtector." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved next protector dependency {dependency}"
