import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadWeaken
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadEndCall
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem fold_same (rows : List (AllocId × BorTag)) (tags : ProtectedTags) (query : BorTag)
    (different : ∀ row∈rows,query≠row.2) :
    (rows.foldl (fun current row => current.remove row.2) tags).contains query = tags.contains query := by
  induction rows generalizing tags with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by intro next member;exact different next (by simp [member]))]
    unfold ProtectedTags.contains
    rw [GeneralBorrowProtectorCacheMap.remove_other tags row.2 query (different row (by simp))]

/-- The real endCall fold retains complete mixed Read data after releasing
only hidden tags. Effective writable leaf permissions and counters remain available for
the next partial source Read and destination Write. -/
noncomputable def end_call (tree : BorrowTree) (location : LocationTree) (global : GlobalState) (frame : FrameState)
    (hidden : ∀ row∈frame.protectedTags.toList,∀ index node,tree.nodeAt index=some node → node.tag=row.2 → node.isExposed=false)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location global.protectedTags anchor selected head tail support writable) :
    GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location (global.endCall frame).protectedTags anchor selected head tail support writable := by
  apply GeneralBorrowExposedScopedInactiveWritableReadWeaken.weaken tree location global.protectedTags (global.endCall frame).protectedTags
    (GeneralBorrowRelease.end_call_weakens global frame) _ anchor selected head tail support writable context data
  intro index node present exposed
  have different : ∀ row∈frame.protectedTags.toList,node.tag≠row.2 := by
    intro row member equal
    have flag := hidden row member index node present equal
    rw [flag] at exposed
    cases exposed
  have same := fold_same frame.protectedTags.toList global.protectedTags node.tag different
  simpa only [GlobalState.endCall,Array.foldl_toList] using same
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadEndCall
