import duplicate_prefix.GeneralBorrowScopedConcreteLenTargetActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableLenCallInput
namespace DuplicatePrefix.GeneralBorrowScopedConcreteLenInputTargetActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralBorrowExposedScopedSharedPathMetadata
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
def held {profileMode : ProfileMode} (s : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag
/-- The two real shared accesses and the actual helper release preserve the
original concrete target's window activity. -/
theorem source {profileMode : ProfileMode} (s : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode)
    (firstOffset : s.first.offset=s.offset) (firstLen : s.first.len=s.len)
    (initial : ActiveWithin s.first.tree s.first.parent .Write s.offset (s.offset+s.len)) :
    let tags := (held s).global.protectedTags
    ActiveWithin ((GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len).releaseProtector
      s.tracker.global.nextPointerTag tags).tree s.first.parent .Write s.offset (s.offset+s.len) := by
  let tags := (held s).global.protectedTags
  have first := GeneralBorrowExposedScopedInactiveWritableSharedTargetActivity.preserve s.first s.firstTags s.selected s.head s.tail (fun _=>true)
    s.firstRaw s.first.parent s.offset (s.offset+s.len) (by simpa only [firstOffset] using (Nat.le_refl s.offset.toNat))
    (by simpa only [firstOffset,firstLen] using (Nat.le_refl (s.offset+s.len).toNat)) initial
  have middle : ActiveWithin s.input.tree s.first.parent .Write s.offset (s.offset+s.len) := by rw [s.firstTreeEq];exact first
  have released := GeneralBorrowScopedConcreteLenTargetActivity.source s.input tags s.selected s.head s.tail s.writable s.raw
    s.first.parent s.offset s.len s.tracker.global.nextPointerTag s.offsetEq s.lenEq s.tagEq s.clean middle
  have actual : child s.input tags .VisitChildrenOfAccessed=GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len := by
    simp only [child,GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,s.treeEq,s.parentTagEq,s.tagEq,s.offsetEq,s.lenEq,s.protectedEq]
    rfl
  rw [actual] at released
  exact released
end
end DuplicatePrefix.GeneralBorrowScopedConcreteLenInputTargetActivity
