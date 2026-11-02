import duplicate_prefix.S02SameDestinationRejectedResultHelper
import duplicate_prefix.GeneralBorrowRawSharedToLenLiteralLedger
namespace DuplicatePrefix.S02SameDestinationRejectedResultLiteralActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section
/-- The exact expression/helper/release tree preserves an old hidden leaf's
activity interval, with no relationship imposed on the two byte intervals. -/
theorem preserves (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+2 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (target : UniIndex) (node : TreeNode) (present : tree.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ input.parent)
    (lower upper : UInt64) (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let final := GeneralBorrowRawSharedToLenLiteralLedger.finalTree tree tracker input.parentTag input.offset input.len input.tagRoom
    GeneralBorrowFreshActiveWithin.ActiveWithin final target .Write lower upper ∧
      ∃ next, final.nodeAt target = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
        next.children = #[] ∧ next.isExposed = false := by
  let expression := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
    input.offset input.len .VisitChildrenOfAccessed).tree
  let nextTracker := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have fresh := GeneralBorrowParentTagInvariant.fresh tree tracker.global runtime
  obtain ⟨expressionActive,next,nextPresent,nextTag,nextParent,nextLeaf,nextHidden⟩ :=
    S02SameDestinationRejectedResultSharedStage.stage tree tracker.global runtime input.parentTag tracker.global.nextPointerTag
      input.parent input.selected target input.maximum input.offset input.len input.positive input.tagged input.distinct input.order
      input.short fresh input.nodeRoom false node present leaf hidden different lower upper activity
  obtain ⟨exprRuntime,capacity,raw,rawTag,rawSelected,rawMaximum,rawOffset,rawLen⟩ :=
    GeneralBorrowRawSharedNext.next_input tree tracker runtime input (by omega) nodeRoom tagRoom
  have nextOther : target ≠ raw.parent := by
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    obtain ⟨contract,readRuntime,⟨readPositive⟩⟩ := GeneralBorrowReadRowRange.access tree tracker.global runtime input.parentTag
      input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .VisitChildrenOfAccessed input.offset input.len input.positive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
    obtain ⟨parentNode,parentPresent⟩ := readPositive.sourcePresent
    have tagged : read.tree.indexOfTag input.parentTag = some input.parent := by
      unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
    have freshRead : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
    have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
    have nonzero : input.len ≠ 0 := by intro zero;have h:=input.positive.positive;rw [zero] at h;contradiction
    obtain ⟨child,lookup,⟨childNode,childPresent,childTag,_parent,_hidden⟩,_old⟩ := GeneralBorrowSharedChildGraph.construct
      read.tree tracker.global readRuntime input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent
      freshRead room false input.offset input.len nonzero readPositive.bounds
    have rawLookup : expression.indexOfTag tracker.global.nextPointerTag = some raw.parent := (congrArg (fun tag => expression.indexOfTag tag) rawTag.symm).trans raw.tagged
    have childSame : child = raw.parent := Option.some.inj (lookup.symm.trans rawLookup)
    intro same
    have targetAtChild : expression.nodeAt child = some next := by
      have nextAt : expression.nodeAt target = some next := nextPresent
      rw [same,←childSame] at nextAt
      exact nextAt
    have nodeSame : next = childNode := Option.some.inj (targetAtChild.symm.trans childPresent)
    have below := GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global runtime target node present
    have tags : node.tag = tracker.global.nextPointerTag := nextTag.symm.trans ((congrArg TreeNode.tag nodeSame).trans childTag)
    rw [tags] at below
    have impossible := UInt64.lt_iff_toNat_lt.mp below
    omega
  obtain ⟨_readDone,_childDone,_capacity,growth,_roots,_runtime,_child,_lookup,_positive⟩ :=
    GeneralBorrowRawSharedResources.resources tree tracker.global runtime input
  have helperRoom : expression.nodes.size+1 < 65536 := by
    have h : expression.nodes.size ≤ tree.nodes.size+1 := growth
    omega
  have retained := S02SameDestinationRejectedResultHelper.helper expression nextTracker allocation exprRuntime raw helperRoom
    target next nextPresent nextLeaf nextHidden nextOther lower upper expressionActive
  rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq] at retained
  simp only [rawTag,rawOffset,rawLen] at retained
  obtain ⟨active,last,found,tag,parent,leaf,hidden⟩ := retained
  exact ⟨active,last,found,tag.trans nextTag,parent.trans nextParent,leaf,hidden⟩
end
end DuplicatePrefix.S02SameDestinationRejectedResultLiteralActivity
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultLiteralActivity.preserves) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved literal activity dependency {dependency}"
