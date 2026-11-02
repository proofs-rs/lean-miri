import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot
import duplicate_prefix.GeneralBorrowRangePreserves

namespace DuplicatePrefix.GeneralBorrowFreshSharedSlotFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def Unexposed (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodeAt index = some node → node.isExposed = false

/-- Structural attachment lookup laws preserve all-unexposed. -/
theorem attached (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (initial : Unexposed tree) (parentPresent : tree.nodeAt parent = some parentNode)
    (freshFlag : newNode.isExposed = false)
    (parentLookup : (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt parent =
      some (GeneralBorrowFreshGraph.updatedParent parentNode index))
    (newLookup : (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt index = some newNode)
    (otherLookup : ∀ query, query ≠ parent → query ≠ index →
      (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query = tree.nodeAt query) :
    Unexposed (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) := by
  intro query node present
  by_cases same : query = parent
  · subst query
    rw [parentLookup] at present
    cases present
    exact initial parent parentNode parentPresent
  · by_cases fresh : query = index
    · subst query
      rw [newLookup] at present
      cases present
      exact freshFlag
    · rw [otherLookup query same fresh] at present
      exact initial query node present

/-- ExposureShape also retains vacancies, so it transfers the universal flag
property without requiring an operation outcome or a present-node bijection. -/
theorem transfer (before after : BorrowTree)
    (same : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (initial : Unexposed before) : Unexposed after := by
  intro query node present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after same query
  rw [show after.nodes.get query = some node from present] at flags
  cases old : before.nodeAt query with
  | none => rw [show before.nodes.get query = none from old] at flags;contradiction
  | some previous =>
    have oldFlag := initial query previous old
    simpa only [show before.nodes.get query = some previous from old,Option.map_some,Option.some.injEq,oldFlag] using flags

/-- Actual Frozen construction preserves every old and new node's unexposed
flag, in either allocator branch, with arbitrary location permissions. -/
theorem of_slot (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : Slot tree depth parent) (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (initial : Unexposed tree) :
    Unexposed (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len) := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    apply transfer (GeneralBorrowFreshMetadataChildShared.stage input) _ (GeneralBorrowFreshMetadataChildShared.exposure input)
    have stagedFlags := attached tree (GeneralBorrowFreshMetadataChildShared.index input) parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent) initial parentPresent rfl
      (GeneralBorrowFreshGraph.parent_lookup _ _ _ _ _ (GeneralBorrowFreshMetadataChildShared.at_end input) parentPresent)
      (GeneralBorrowFreshGraph.new_lookup _ _ _ _ _ (GeneralBorrowFreshMetadataChildShared.at_end input) parentPresent)
      (fun query notParent notNew => GeneralBorrowFreshGraph.other_lookup _ _ _ _ _ _ (GeneralBorrowFreshMetadataChildShared.at_end input) parentPresent notParent notNew)
    simpa only [input,Unexposed,GeneralBorrowFreshMetadataChildShared.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using stagedFlags
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    apply transfer (GeneralBorrowFreshMetadataChildSharedReuse.stage input) _ (GeneralBorrowFreshMetadataChildSharedReuse.exposure input)
    have stagedFlags := attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode newTag parent) initial parentPresent rfl
      (GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup _ _ _ _ _ vacant parentPresent)
      (GeneralBorrowFreshMetadataChildReuseGraph.new_lookup _ _ _ _ _ vacant parentPresent)
      (fun query notParent notNew => GeneralBorrowFreshMetadataChildReuseGraph.other_lookup _ _ _ _ _ _ vacant parentPresent notParent notNew)
    simpa only [input,GeneralBorrowFreshMetadataChildSharedReuse.index,Unexposed,GeneralBorrowFreshMetadataChildSharedReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt] using stagedFlags

end DuplicatePrefix.GeneralBorrowFreshSharedSlotFlags
