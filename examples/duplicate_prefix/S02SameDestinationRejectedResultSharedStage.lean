import duplicate_prefix.S02SameDestinationRejectedResultActivity
import duplicate_prefix.S02SameDestinationRejectedResultLeaf
import duplicate_prefix.S02SameDestinationRejectedResultReadActivity
namespace DuplicatePrefix.S02SameDestinationRejectedResultSharedStage
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Read plus actual shared construction retains a distinct old hidden leaf
and its exact activity window. No containment between the two intervals is required. -/
theorem stage (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent selected query : UniIndex) (maximum : Option BorTag)
    (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags parent selected maximum offset len)
    (tagged : tree.indexOfTag parentTag = some parent)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (room : tree.nodes.size+1 ≤ 4294967295) (held : Bool)
    (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ parent)
    (lower upper : UInt64) (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree query .Write lower upper) :
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read global.protectedTags .VisitChildrenOfAccessed
    let final := (read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen held).tree
    GeneralBorrowFreshActiveWithin.ActiveWithin final query .Write lower upper ∧
      ∃ next, final.nodeAt query = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
        next.children = #[] ∧ next.isExposed = false := by
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read global.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree global runtime
    parentTag parent selected maximum tagged (Size.ofBytes offset) (Size.ofBytes len)
    .VisitChildrenOfAccessed offset len positive distinct order short (Nat.le_refl _) (Nat.le_refl _)
  have active := S02SameDestinationRejectedResultReadActivity.concrete tree global runtime parentTag
    parent selected query maximum offset len positive tagged node present leaf hidden different
    lower upper activity .VisitChildrenOfAccessed
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have readPresent : read.tree.nodeAt query = some node := by
    change read.tree.nodes.get query = some node
    rw [contract.nodes]; exact present
  have readTagged : read.tree.indexOfTag parentTag = some parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]; exact tagged
  have readFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [contract.tags]; exact fresh
  have readRoom : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes]; exact room
  have nonzero : len ≠ 0 := by intro zero;have h:=positive.positive;rw [zero] at h;contradiction
  have finalActivity := S02SameDestinationRejectedResultActivity.construct read.tree global afterRuntime
    parentTag newTag parent parentNode readTagged parentPresent readFresh readRoom held offset len nonzero
    afterPositive.bounds query lower upper node readPresent active
  obtain ⟨next,found,tag,parentEq,children,exposure⟩ := S02SameDestinationRejectedResultLeaf.construct
    read.tree global afterRuntime parentTag newTag parent parentNode readTagged parentPresent readFresh readRoom held
    offset len nonzero afterPositive.bounds query node readPresent different
  exact ⟨finalActivity,next,found,tag,parentEq,children.trans leaf,exposure.trans hidden⟩
end DuplicatePrefix.S02SameDestinationRejectedResultSharedStage
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultSharedStage.stage) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved shared stage activity dependency {dependency}"
