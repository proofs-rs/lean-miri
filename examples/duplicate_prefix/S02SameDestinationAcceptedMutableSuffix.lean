import duplicate_prefix.S02SameDestinationAcceptedDefaultStage
import duplicate_prefix.S02SameDestinationAcceptedDefaultPhase
import duplicate_prefix.S02SameDestinationAcceptedHelperSuffix
import duplicate_prefix.GeneralBorrowRawDefaultResources
namespace DuplicatePrefix.S02SameDestinationAcceptedMutableSuffix
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Both actual mutable constructors and the helper's release/endCall preserve a disjoint original hidden return leaf. -/
theorem destination (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (target selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : input.offset.toNat+input.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree tracker.global.protectedTags (some target) (some selected) maximum lower width)
    (node : TreeNode) (present : tree.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ input.parent)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower (lower+width)) :
    let expr := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let nextTracker := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    ∃ next : GeneralBorrowRawFnEntry.Input expr nextTracker.global,
      next.parentTag = tracker.global.nextPointerTag ∧ next.offset = input.offset ∧ next.len = input.len ∧
      let borrowed := GeneralBorrowRawFnEntryArgument.finalTree expr nextTracker next.parentTag next.offset next.len
      let held := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker nextTracker next.tagRoom) nextTracker.global.nextPointerTag
      let released := (borrowed.releaseProtector nextTracker.global.nextPointerTag held.protectedTags).tree
      let returned := held.endCall (({} : FrameState).addProtector allocation nextTracker.global.nextPointerTag)
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive released returned.protectedTags (some target) (some selected) maximum lower width) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write lower (lower+width) ∧
      ∃ finalNode, released.nodeAt target = some finalNode ∧ finalNode.tag = node.tag ∧ finalNode.parent = node.parent ∧ finalNode.children = #[] ∧ finalNode.isExposed = false := by
  let expr := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let nextTracker := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  obtain ⟨_,registeredRuntime,⟨registeredPositive⟩,fresh,_unheld⟩ := GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime input.parent input.selected input.maximum input.offset input.len input.positive
  let advanced := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  obtain ⟨active,middle,middlePresent,middleTag,middleParent,middleLeaf,middleHidden⟩ :=
    S02SameDestinationAcceptedDefaultStage.stage tree advanced registeredRuntime input.parentTag tracker.global.nextPointerTag input.parent input.selected target input.maximum input.offset input.len registeredPositive input.tagged input.distinct input.order input.short fresh input.nodeRoom node present leaf hidden different lower (lower+width) activity
  have middleAtExpr : expr.nodeAt target = some middle := middlePresent
  have exprActive : GeneralBorrowFreshActiveWithin.ActiveWithin expr target .Write lower (lower+width) := active
  obtain ⟨_,_,_,⟨exprPositive⟩⟩ := S02SameDestinationAcceptedDefaultPhase.literal tree tracker.global runtime input (some target) (some selected) maximum lower width outside positive
  obtain ⟨exprRuntime,capacity,stepRoom,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ := GeneralBorrowRawDefaultResources.resources tree tracker runtime input headroom tagRoom
  have notNextParent : target ≠ next.parent := by
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read advanced.protectedTags .VisitChildrenOfAccessed
    obtain ⟨contract,readRuntime,⟨readPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree advanced registeredRuntime input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short (Nat.le_refl _) (Nat.le_refl _)
    obtain ⟨parentNode,parentPresent⟩ := readPositive.sourcePresent input.parent rfl
    have tagged : read.tree.indexOfTag input.parentTag = some input.parent := by unfold BorrowTree.indexOfTag;rw [contract.tags];exact input.tagged
    have freshRead : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
    have room : read.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
    have nonzero : input.len ≠ 0 := by intro zero;have p:=input.positive.positive;rw [zero] at p;contradiction
    obtain ⟨child,lookup,⟨childNode,childPresent,childTag,_hidden⟩,_paths,_old⟩ := GeneralBorrowDefaultChildMetadata.construct read.tree advanced readRuntime input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshRead room input.offset input.len nonzero readPositive.bounds
    have nextLookup : expr.indexOfTag tracker.global.nextPointerTag = some next.parent := by simpa only [nextTag] using next.tagged
    have childSame : child = next.parent := Option.some.inj (lookup.symm.trans nextLookup)
    intro same
    have targetAtChild : expr.nodeAt child = some middle := by simpa only [same,childSame] using middleAtExpr
    have nodeEq : middle = childNode := Option.some.inj (targetAtChild.symm.trans childPresent)
    have below := GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global runtime target node present
    have tags : node.tag = tracker.global.nextPointerTag := middleTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans childTag)
    rw [tags] at below
    have impossible := UInt64.lt_iff_toNat_lt.mp below
    omega
  have final := S02SameDestinationAcceptedHelperSuffix.destination expr nextTracker allocation exprRuntime next stepRoom target selected maximum lower width (by simpa only [nextOffset,nextLen] using outside) exprPositive middle middleAtExpr middleLeaf middleHidden notNextParent exprActive
  obtain ⟨positive,active,last,lastPresent,lastTag,lastParent,lastLeaf,lastHidden⟩ := final
  exact ⟨next,nextTag,nextOffset,nextLen,positive,active,last,lastPresent,lastTag.trans middleTag,lastParent.trans middleParent,lastLeaf,lastHidden⟩
end
end DuplicatePrefix.S02SameDestinationAcceptedMutableSuffix
