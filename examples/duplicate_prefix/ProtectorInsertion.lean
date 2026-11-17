import Lean
import Miri.TreeBorrows.GlobalState
namespace DuplicatePrefix.ProtectorInsertion
open Miri Miri.Memory Miri.TreeBorrows
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem get_other (map : ProtectedTags) (new old : BorTag) (kind : ProtectorKind) (different : old ≠ new) :
    (map.insert new kind).get old = map.get old := by
  have predicate : (fun row : BorTag × ProtectorKind => decide ((row.1 != new) = true ∧ (row.1 == old) = true)) =
      (fun row : BorTag × ProtectorKind => row.1 == old) := by
    funext row
    by_cases same : row.1 = old
    · simp [same,different]
    · simp [same]
  simp only [ProtectedTags.get,ProtectedTags.insert,Array.find?_push,Array.find?_filter]
  rw [predicate]
  simp [different,Ne.symm different]

theorem contains_other (map : ProtectedTags) (new old : BorTag) (kind : ProtectorKind) (different : old ≠ new) :
    (map.insert new kind).contains old = map.contains old := by
  unfold ProtectedTags.contains
  rw [get_other map new old kind different]

#print axioms contains_other
end DuplicatePrefix.ProtectorInsertion
