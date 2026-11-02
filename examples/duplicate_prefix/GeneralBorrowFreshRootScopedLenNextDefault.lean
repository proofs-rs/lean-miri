import duplicate_prefix.GeneralBorrowFreshRootScopedSharedToLenLedger
import duplicate_prefix.GeneralBorrowFreshRootScopedDefault
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedLenNextDefault
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- The exact len result graph and restored CURRENT scoped owner form the next
Default borrowing packet internally. Only initial source identity and initial
numeric tag headroom are additional data; no next-operation success is assumed. -/
theorem forms (before after : BorrowTree) (selected parent : UniIndex)
    (beforeTracker afterTracker : MachineHooks.BorrowState)
    (graph : GeneralBorrowFreshRootScopedSharedToLenLedger.Graph before after selected beforeTracker afterTracker)
    (parentTag maximum : BorTag) (offset len : UInt64) (node : TreeNode)
    (present : before.nodeAt parent = some node) (tag : node.tag = parentTag)
    (positive : GeneralBorrowFreshRootScopedRow.Positive after afterTracker.global.protectedTags parent selected maximum offset len)
    (tagMargin : beforeTracker.global.nextPointerTag.value.toNat+2 < 18446744073709551615) :
    ∃ next : GeneralBorrowFreshRootScopedDefault.Input after afterTracker.global,
      next.parentTag = parentTag ∧ next.parent = parent ∧ next.selected = selected ∧
      next.maximum = maximum ∧ next.offset = offset ∧ next.len = len := by
  obtain ⟨_,_,_,_,_,tagged⟩ := graph.oldNodes parent node present
  have currentTagged : after.indexOfTag parentTag = some parent := by
    rw [←tag]
    exact tagged
  have fresh : afterTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change afterTracker.global.nextPointerTag.value.toNat < 18446744073709551615
    rw [graph.tagCounter]
    exact tagMargin
  let next : GeneralBorrowFreshRootScopedDefault.Input after afterTracker.global := {
    parentTag:=parentTag,parent:=parent,selected:=selected,maximum:=maximum,offset:=offset,len:=len,
    tagged:=currentTagged,positive:=positive,distinct:=graph.distinct,short:=graph.short,
    nodeRoom:=by have bound:=graph.short;omega,tagRoom:=fresh }
  exact ⟨next,rfl,rfl,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedLenNextDefault
