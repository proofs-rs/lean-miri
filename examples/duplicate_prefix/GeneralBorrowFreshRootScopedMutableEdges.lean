import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultEdges
import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntryEdges
import duplicate_prefix.GeneralBorrowFreshRootScopedDefaultResources
import duplicate_prefix.GeneralBorrowParentRestoreSupport
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedMutableEdges
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Exact two temporary edges and absence of both temporary protectors. -/
theorem edges (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedDefault.Input tree tracker.global)
    (headroom : tree.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let defaultTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
      input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
    ∃ secondFresh : allocated.global.nextPointerTag.value < 18446744073709551615,
    let helperTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree defaultTree allocated tracker.global.nextPointerTag input.offset input.len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker allocated secondFresh) allocated.global.nextPointerTag
    let final := held.global.endCall (({} : FrameState).addProtector allocation allocated.global.nextPointerTag)
    ∃ parent child parentNode childNode,
      helperTree.indexOfTag tracker.global.nextPointerTag = some parent ∧
      helperTree.indexOfTag allocated.global.nextPointerTag = some child ∧
      helperTree.nodeAt parent = some parentNode ∧ helperTree.nodeAt child = some childNode ∧
      parentNode.tag = tracker.global.nextPointerTag ∧ parentNode.parent = some input.parent ∧
      childNode.tag = allocated.global.nextPointerTag ∧ childNode.parent = some parent ∧
      final.protectedTags.contains parentNode.tag = false ∧ final.protectedTags.contains childNode.tag = false := by
  let defaultTree := (GeneralBorrowFreshRootScopedDefaultExpression.child tree tracker.global.protectedTags
    input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have resources := GeneralBorrowFreshRootScopedDefaultResources.resources tree tracker runtime input headroom tagsRoom
  dsimp only at resources
  obtain ⟨defaultRuntime,_,_,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ := resources
  obtain ⟨⟨defaultIndex,defaultNode,defaultLookup,defaultPresent,defaultTag,defaultEdge⟩,_⟩ :=
    GeneralBorrowFreshRootScopedDefaultEdges.edges tree tracker runtime input
  have parentLookup : defaultTree.indexOfTag tracker.global.nextPointerTag = some next.parent :=
    (congrArg (fun tag => defaultTree.indexOfTag tag) nextTag).symm.trans next.tagged
  have sameIndex : defaultIndex = next.parent := Option.some.inj (defaultLookup.symm.trans parentLookup)
  subst defaultIndex
  have helperEdges := GeneralBorrowFreshRootScopedFnEntryEdges.edges defaultTree allocated {} allocation defaultRuntime next
  dsimp only at helperEdges
  rw [nextTag,nextOffset,nextLen] at helperEdges
  obtain ⟨⟨child,childNode,childLookup,childPresent,childTag,childEdge⟩,oldFields⟩ := helperEdges
  obtain ⟨parentNode,parentPresent,parentTag,parentEdge⟩ := oldFields next.parent defaultNode defaultPresent
  let helperTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree defaultTree allocated tracker.global.nextPointerTag input.offset input.len
  have helperRuntime := (GeneralBorrowFreshRootScopedFnEntryResources.resources defaultTree allocated {} allocation defaultRuntime next).1
  change DuplicatePrefixBorrowContract.RuntimeFacts
    (GeneralBorrowFreshRootScopedFnEntryArgument.finalTree defaultTree allocated next.parentTag next.offset next.len) _ at helperRuntime
  rw [nextTag,nextOffset,nextLen] at helperRuntime
  have lookupParent := helperRuntime.formed.allocator.nodeTags next.parent parentNode parentPresent
  rw [parentTag,defaultTag] at lookupParent
  have secondFresh := next.tagRoom
  have unheld := (GeneralBorrowDefaultTagAllocation.prepare tree tracker.global input.tagRoom runtime
    input.parent input.selected (some input.maximum) input.offset input.len input.positive.base).2.2.2.2
  have different : tracker.global.nextPointerTag ≠ allocated.global.nextPointerTag := by
    intro equal
    have same := congrArg (fun tag : BorTag => tag.value.toNat) equal
    change tracker.global.nextPointerTag.value.toNat = (TypedRetagEmpty.successorTag tracker.global.nextPointerTag input.tagRoom).value.toNat at same
    rw [GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom] at same
    omega
  refine ⟨secondFresh,next.parent,child,parentNode,childNode,lookupParent,childLookup,parentPresent,childPresent,
    parentTag.trans defaultTag,parentEdge.trans defaultEdge,childTag,childEdge,?_,?_⟩
  · rw [parentTag,defaultTag]
    change ((tracker.global.protectedTags.insert allocated.global.nextPointerTag .StrongProtector).remove allocated.global.nextPointerTag).contains tracker.global.nextPointerTag = false
    rw [GeneralBorrowParentRestoreSupport.contains_other _ _ _ different,
      ProtectorInsertion.contains_other _ _ _ _ different]
    exact unheld
  · rw [childTag]
    change ((tracker.global.protectedTags.insert allocated.global.nextPointerTag .StrongProtector).remove allocated.global.nextPointerTag).contains allocated.global.nextPointerTag = false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
end DuplicatePrefix.GeneralBorrowFreshRootScopedMutableEdges
