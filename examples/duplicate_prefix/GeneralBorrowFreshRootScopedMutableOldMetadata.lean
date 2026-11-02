import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultResources
import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntryResources
import duplicate_prefix.GeneralBorrowDefaultChildMetadata
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedMutableOldMetadata
open Miri Miri.Interpreter Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem default_old (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedDefault.Input tree tracker.global)

    (query : UniIndex) (old : TreeNode) (oldPresent : tree.nodeAt query = some old) :
    let finalTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    ∃ node, finalTree.nodeAt query = some node ∧ node.tag = old.tag ∧ node.isExposed = old.isExposed := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ :=
    GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime
      input.parent input.selected (some input.maximum) input.offset input.len input.positive.base
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree registration registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read .VisitChildrenOfAccessed input.offset input.len input.positive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨_,_,_,_,oldFields⟩ := GeneralBorrowDefaultChildMetadata.construct accessed.tree registration afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    input.offset input.len nonzero afterPositive.base.bounds
  apply oldFields query old
  change accessed.tree.nodes.get query = some old
  rw [contract.nodes]
  exact oldPresent

private theorem helper_old (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedFnEntry.Input tree tracker.global)

    (query : UniIndex) (old : TreeNode) (oldPresent : tree.nodeAt query = some old) :
    let finalTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    ∃ node, finalTree.nodeAt query = some node ∧ node.tag = old.tag ∧ node.isExposed = old.isExposed := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent input.parent rfl
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨_,_,_,_,oldFields⟩ := GeneralBorrowProtectedChildMetadata.construct accessed.tree registration.1 afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    input.offset input.len nonzero afterPositive.base.bounds
  apply oldFields query old
  change accessed.tree.nodes.get query = some old
  rw [contract.nodes]
  exact oldPresent

/-- Both real temporary constructors retain an arbitrary original node's tag
and exposure flag. Old source metadata is a CURRENT phase invariant. -/
theorem old_node (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) :
    let defaultTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
      input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    let helperTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree defaultTree allocated tracker.global.nextPointerTag input.offset input.len
    ∃ finalNode, helperTree.nodeAt query = some finalNode ∧ finalNode.tag = node.tag ∧ finalNode.isExposed = node.isExposed := by
  let defaultTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
    input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have resources := GeneralBorrowFreshRootScopedDefaultResources.resources tree tracker runtime input headroom tagsRoom
  dsimp only at resources
  obtain ⟨defaultRuntime,_,_,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ := resources
  obtain ⟨middle,middlePresent,middleTag,middleHidden⟩ := default_old tree tracker runtime input query node present
  have last := helper_old defaultTree allocated {} allocation defaultRuntime next query middle middlePresent
  dsimp only at last
  rw [nextTag,nextOffset,nextLen] at last
  obtain ⟨finalNode,finalPresent,finalTag,finalHidden⟩ := last
  exact ⟨finalNode,finalPresent,finalTag.trans middleTag,finalHidden.trans middleHidden⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedMutableOldMetadata
