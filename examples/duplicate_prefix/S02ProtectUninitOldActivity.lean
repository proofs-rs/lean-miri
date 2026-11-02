import duplicate_prefix.S02FnEntryOldActivity
import duplicate_prefix.S02FnEntryOldOther
import duplicate_prefix.S02FnEntryFreshNode

namespace DuplicatePrefix.S02ProtectUninitOldActivity
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Full actual protected FnEntry and its literal uninit Write preserve an
older hidden leaf's activity. Old-node geometry and fresh-tag highwater derive
the second access's distinct hidden-leaf condition internally. -/
theorem preserved (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : query ≠ input.parent)
    (lower upper : UInt64) (active : ActiveWithin tree query .Write lower upper) :
    let retagged := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let global := TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom
    let written := (retagged.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ActiveWithin written query .Write lower upper := by
  have afterActive := S02FnEntryOldActivity.preserved tree tracker borrowFrame allocation runtime input query node present leaf hidden
    different lower upper active
  obtain ⟨afterNode,afterPresent,afterTag,_parent,afterChildren,afterHidden⟩ := S02FnEntryOldOther.preserved tree tracker borrowFrame allocation
    runtime input query node present different
  obtain ⟨post,_capacity,_growth,_roots,_held,_frame,_fresh,child,tagged,⟨positive⟩,_activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker borrowFrame allocation runtime input
  obtain ⟨freshChild,freshNode,freshTagged,freshPresent,freshTag,_freshParent,_freshLeaf,_freshHidden⟩ :=
    S02FnEntryFreshNode.node tree tracker borrowFrame allocation runtime input
  have childEq : freshChild = child := Option.some.inj (freshTagged.symm.trans tagged)
  subst freshChild
  have below := GeneralBorrowForestTagHighWater.mapped tree tracker.global.protectedTags tracker.global.nextPointerTag node.tag
    runtime.below query (runtime.formed.allocator.nodeTags query node present)
  have differentChild : query ≠ child := by
    intro same
    rw [same] at afterPresent
    have nodeEq : afterNode = freshNode := Option.some.inj (afterPresent.symm.trans freshPresent)
    have tagEq : node.tag = tracker.global.nextPointerTag := afterTag.symm.trans ((congrArg TreeNode.tag nodeEq).trans freshTag)
    rw [tagEq] at below
    omega
  exact S02HiddenLeafActivityRange.concrete _ _ post tracker.global.nextPointerTag child input.selected query input.maximum input.offset input.len
    positive tagged afterNode afterPresent (afterChildren.trans leaf) (afterHidden.trans hidden) differentChild lower upper afterActive
    .Write .VisitChildrenOfAccessed

end DuplicatePrefix.S02ProtectUninitOldActivity

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02ProtectUninitOldActivity.preserved) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
