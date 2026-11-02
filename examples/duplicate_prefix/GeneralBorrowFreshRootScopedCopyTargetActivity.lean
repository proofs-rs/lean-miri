import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowFreshRootScopedCopyInput
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedCopyTargetActivity
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The literal adjacent same-tag copy Read then Write preserve an arbitrary
older owner's bytewise activity, from the current copy input and current
owner activity. The access completion/runtime needed for the second request
is derived, not supplied as future data. -/
theorem accesses (tree : BorrowTree) (global : GlobalState) (tag : BorTag)
    (offset sliceLen count : UInt64) (input : GeneralBorrowFreshRootScopedCopyInput.Input tree global tag offset sliceLen count)
    (target : UniIndex) (active : ActiveWithin tree target .Write offset (offset+sliceLen)) :
    let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read global.protectedTags .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write global.protectedTags .VisitChildrenOfAccessed
    ActiveWithin read.tree target .Write offset (offset+sliceLen) ∧
      ActiveWithin write.tree target .Write offset (offset+sliceLen) := by
  let read := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read global.protectedTags .VisitChildrenOfAccessed
  have bounds := input.positive.base.bounds
  have twice := input.twice
  have cap := tree.locations.size.bytes.toNat_lt
  have fullFits : offset.toNat+sliceLen.toNat < 2^64 := by omega
  have firstFits : offset.toNat+count.toNat < 2^64 := by omega
  have secondFits : offset.toNat+count.toNat+count.toNat < 2^64 := by omega
  have full : (offset+sliceLen).toNat = offset.toNat+sliceLen.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits]
  have first : (offset+count).toNat = offset.toNat+count.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt firstFits]
  have second : (offset+count+count).toNat = offset.toNat+count.toNat+count.toNat := by
    rw [UInt64.toNat_add,first,Nat.mod_eq_of_lt secondFits]
  have readActive : ActiveWithin read.tree target .Write offset (offset+sliceLen) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree tag (Size.ofBytes offset) (Size.ofBytes count) .Read
      global.protectedTags .VisitChildrenOfAccessed target offset (offset+sliceLen) input.runtime.formed.well
      (by change offset.toNat+count.toNat ≤ tree.locations.size.bytes.toNat;omega)
      (by change offset.toNat ≤ offset.toNat;omega)
      (by change (offset+count).toNat ≤ (offset+sliceLen).toNat;omega) active
  have actual := GeneralBorrowFreshRootScopedCopyInput.accesses tree global tag offset sliceLen count input
  have readBounds : (offset+count).toNat+count.toNat ≤ read.tree.locations.size.bytes.toNat := by
    rw [actual.1.capacity]
    omega
  have writeActive := GeneralBorrowFreshActiveWithinAccess.normal read.tree tag
    (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write global.protectedTags .VisitChildrenOfAccessed
    target offset (offset+sliceLen) actual.1.well readBounds
    (by change offset.toNat ≤ (offset+count).toNat;omega)
    (by change (offset+count+count).toNat ≤ (offset+sliceLen).toNat;omega) readActive
  exact ⟨readActive,writeActive⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedCopyTargetActivity
