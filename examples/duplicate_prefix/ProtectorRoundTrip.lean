import duplicate_prefix.ProtectorInsertion

namespace DuplicatePrefix.ProtectorRoundTrip
open Miri.Memory Miri.TreeBorrows

set_option autoImplicit false in
theorem get_remove_other (tags : ProtectedTags) (removed query : BorTag)
    (different : query ≠ removed) :
    (tags.remove removed).get query = tags.get query := by
  have predicate : (fun row : BorTag × ProtectorKind =>
      decide ((row.1 != removed) = true ∧ (row.1 == query) = true)) =
      (fun row : BorTag × ProtectorKind => row.1 == query) := by
    funext row
    by_cases same : row.1 = query
    · simp [same,different]
    · simp [same]
  simp only [ProtectedTags.get,ProtectedTags.remove,Array.find?_filter]
  rw [predicate]

set_option autoImplicit false in
/-- Ending a real singleton protector frame preserves every other tag's
lookup, including tags that were already protected before the call. -/
theorem singleton_get (global : GlobalState) (id : AllocId)
    (child query : BorTag) (kind : ProtectorKind) (different : query ≠ child) :
    (({global with protectedTags := global.protectedTags.insert child kind}).endCall
      (({} : FrameState).addProtector id child)).protectedTags.get query =
      global.protectedTags.get query := by
  change ((global.protectedTags.insert child kind).remove child).get query = _
  rw [get_remove_other _ child query different,
    ProtectorInsertion.get_other global.protectedTags child query kind different]

set_option autoImplicit false in
theorem singleton_contains (global : GlobalState) (id : AllocId)
    (child query : BorTag) (kind : ProtectorKind) (different : query ≠ child) :
    (({global with protectedTags := global.protectedTags.insert child kind}).endCall
      (({} : FrameState).addProtector id child)).protectedTags.contains query =
      global.protectedTags.contains query := by
  unfold ProtectedTags.contains
  rw [singleton_get global id child query kind different]

end DuplicatePrefix.ProtectorRoundTrip
