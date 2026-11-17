import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedGraphMetadata
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableTargetActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAsMutRawReady
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRange
import duplicate_prefix.GeneralBorrowForestCopyBorrow
import duplicate_prefix.PositiveRootCopyBounds
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedTargetActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowFreshActiveWithin
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
attribute [local irreducible] UniValMap.insert UniValMap.orInsert
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual ordinary mutable expression, protected helper formation and real
helper release preserve the original FnEntry target's source window activity.
The only activity input belongs to the initial pre-expression source tree. -/
theorem before_copy (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode)
    (call : GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.InputFor profileMode)
    (origin : GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call)
    (active : ActiveWithin expression.entry.allocation.extra expression.data.input.parent .Write expression.offset (expression.offset+expression.len)) :
    ActiveWithin (GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call)
      expression.data.input.parent .Write expression.offset (expression.offset+expression.len) := by
  let first:=expression.data.input
  let helper:=call.data.input
  have firstActive : ActiveWithin first.tree first.parent .Write expression.offset (expression.offset+expression.len) := by
    rw [expression.data.treeEq];exact active
  have expressionActive:=GeneralBorrowExposedScopedInactiveWritableTargetActivity.default_target first expression.tracker.global.protectedTags
    expression.selected expression.head expression.tail expression.data.resources first.parent expression.offset (expression.offset+expression.len)
    (by rw [expression.data.offsetEq];exact Nat.le_refl _) (by rw [expression.data.offsetEq,expression.data.lenEq];exact Nat.le_refl _) firstActive
  have expressionTreeEq : GeneralBorrowExposedScopedInactiveWritableTargetActivity.defaultChild first expression.tracker.global.protectedTags=
      GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.expressionTree expression := by
    simp only [GeneralBorrowExposedScopedInactiveWritableTargetActivity.defaultChild,first,GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.expressionTree,
      GeneralBorrowExposedScopedInactiveWritableDefaultExpression.child,GeneralBorrowExposedScopedInactiveWritableDefaultExpression.read,
      expression.data.treeEq,expression.data.parentTagEq,expression.data.newTagEq,expression.data.offsetEq,expression.data.lenEq]
  have helperTreeEq : helper.tree=GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.expressionTree expression := by
    rw [call.data.treeEq,origin.entry];rfl
  have helperActive : ActiveWithin helper.tree first.parent .Write helper.offset (helper.offset+helper.len) := by
    rw [helperTreeEq,call.data.offsetEq,call.data.lenEq,origin.offset,origin.len,←expressionTreeEq]
    exact expressionActive
  have nodeTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    intro query node present
    rw [call.data.treeEq] at present ⊢
    exact call.data.nodeTags query node present
  obtain ⟨raw,supportEq⟩:=GeneralBorrowExposedScopedInactiveWritableMutableEntryInput.register helper call.tracker.global.protectedTags
    call.selected call.head call.tail call.data.resources nodeTags
  have kept:=GeneralBorrowExposedScopedInactiveWritableTargetActivity.mutable_release_target helper
    (call.tracker.global.protectedTags.insert helper.newTag .StrongProtector) call.selected call.head call.tail raw call.clean first.parent helperActive
  simpa only [GeneralBorrowExposedScopedInactiveWritableTargetActivity.mutableChild,helper,first,
    GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released,GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.childTree,
    GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held,GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,
    TypedBorrowSteps.registeredTracker,TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker,
    call.data.treeEq,call.data.parentTagEq,call.data.newTagEq,call.data.offsetEq,call.data.lenEq,origin.offset,origin.len] using kept

def copiedTree (call : GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.InputFor profileMode) (count : UInt64) :=
  let tags:=((GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call).global.endCall
    (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)).protectedTags
  let read:=(GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call).performBorrowAccessRange
    (.concrete call.tracker.global.nextPointerTag) (Size.ofBytes call.offset) (Size.ofBytes count) .Read tags .VisitChildrenOfAccessed
  (read.tree.performBorrowAccessRange (.concrete call.tracker.global.nextPointerTag)
    (Size.ofBytes (call.offset+count)) (Size.ofBytes count) .Write tags .VisitChildrenOfAccessed).tree

/-- The same source-formed target activity survives both actual shifted copy
accesses. Read geometry is derived from raw helper inputs; no final activity,
successful copy/access or full-allocation owner is supplied. -/
theorem after_copy (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode)
    (call : GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.InputFor profileMode)
    (origin : GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call)
    (active : ActiveWithin expression.entry.allocation.extra expression.data.input.parent .Write expression.offset (expression.offset+expression.len))
    (count : UInt64) (within : count≤call.len/2) :
    ActiveWithin (copiedTree call count) expression.data.input.parent .Write expression.offset (expression.offset+expression.len) := by
  let tree:=GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call
  let tags:=((GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call).global.endCall
    (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)).protectedTags
  let read:=tree.performBorrowAccessRange (.concrete call.tracker.global.nextPointerTag) (Size.ofBytes call.offset) (Size.ofBytes count)
    .Read tags .VisitChildrenOfAccessed
  have initial:=before_copy expression call origin active
  have ready:=GeneralBorrowExposedScopedInactiveWritableAsMutRawReady.ready call.entry.allocation.extra call.tracker call.id call.parentTag
    call.offset call.len call.selected call.head call.tail call.data call.rangePositive call.clean
  obtain ⟨context,owned,well,capacity⟩:=ready.2
  have graph:=GeneralBorrowExposedScopedInactiveWritableAcceptedGraphMetadata.metadata expression call origin
  have treeCapacity : tree.locations.size=call.entry.allocation.extra.locations.size := capacity
  have bounds : call.offset.toNat+call.len.toNat≤tree.locations.size.bytes.toNat := by
    rw [treeCapacity,call.capacity];exact call.bounds
  have twice:=(PositiveRootCopyBounds.guarded call.len count call.offset call.entry.allocation.byteSize.bytes within call.bounds).2.1
  have ranges:=GeneralBorrowForestCopyBorrow.arithmetic call.offset call.len count tree.locations.size.bytes bounds twice
  have raw : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location tags
      (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail
      (fun position=>call.data.resources.component.support position ∨ position=(GeneralBorrowFreshMetadataChildMutable.index call.data.input).toNat) (fun _=>true)))
      call.offset (call.offset+call.len) tree.locations := by
    intro position valid positive lower upper
    exact owned position valid positive lower upper
  have first:=GeneralBorrowExposedScopedInactiveWritableReadRange.access tree tags call.tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail
    (Size.ofBytes call.offset) (Size.ofBytes count) context
    (fun position=>call.data.resources.component.support position ∨ position=(GeneralBorrowFreshMetadataChildMutable.index call.data.input).toNat)
    (fun _=>true) graph.2.2.2.1 graph.2.2.2.2.1 well call.offset (call.offset+call.len) raw ranges.1 (Nat.le_refl _) ranges.2.2.2.1
  have readActive : ActiveWithin read.tree expression.data.input.parent .Write expression.offset (expression.offset+expression.len) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree call.tracker.global.nextPointerTag (Size.ofBytes call.offset) (Size.ofBytes count)
      .Read tags .VisitChildrenOfAccessed expression.data.input.parent expression.offset (expression.offset+expression.len)
      well ranges.1 (by rw [origin.offset];exact Nat.le_refl _) (by simpa only [origin.offset,origin.len,Size.ofBytes] using ranges.2.2.2.1) initial
  exact GeneralBorrowFreshActiveWithinAccess.normal read.tree call.tracker.global.nextPointerTag (Size.ofBytes (call.offset+count)) (Size.ofBytes count)
    .Write tags .VisitChildrenOfAccessed expression.data.input.parent expression.offset (expression.offset+expression.len)
    first.2.2.1 (by rw [first.2.2.2];exact ranges.2.1)
    (by simpa only [origin.offset,Size.ofBytes] using ranges.2.2.1) (by simpa only [origin.offset,origin.len,Size.ofBytes] using ranges.2.2.2.2) readActive

end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAcceptedTargetActivity
