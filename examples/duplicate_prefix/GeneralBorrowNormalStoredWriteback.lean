import duplicate_prefix.GeneralBorrowSharedProfileRead
namespace DuplicatePrefix.GeneralBorrowNormalStoredWriteback
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every explicitly stored actual normal-result state reaches real permission
write-back unchanged; the subsequent cache loop never edits permission slots. -/
theorem stored (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root query : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (state : LocationState)
    (present : ((source_normal_projection tree location protections).performAccess root.toNat kind mode).tree.locationStates[query.toNat]? = some (some state)) :
    (tree.performNormalAccessAt location root kind protections mode).location.perms.get query = some state := by
  rw [source_normal_perms]
  unfold_clean_write_states
  simp only [Id.run,bind,pure,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  change (forIn _ location (source_write_scan _)).perms.get query = some state
  rw [source_write_list_get]
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  have row := (Array.getElem?_eq_some_iff.mp present).2
  simp [List.mem_range',bounded,row,Option.or]
end DuplicatePrefix.GeneralBorrowNormalStoredWriteback
