import Miri.TreeBorrows.GlobalState

/-! Lookup stability for actual ProtectedTags.insert. -/
namespace DuplicatePrefix.ProtectedTagsFacts
open Miri.TreeBorrows

theorem insert_preserves_other (tags : ProtectedTags)
    (root child : Miri.Memory.BorTag) (kind : ProtectorKind)
    (distinct : root ≠ child) :
    (tags.insert child kind).get root = tags.get root := by
  have filtered :
      (tags.entries.filter (fun entry => entry.1 != child)).find?
          (fun entry => entry.1 == root) =
        tags.entries.find? (fun entry => entry.1 == root) := by
    rw [Array.find?_filter]
    congr 1
    funext entry
    by_cases hq : (entry.1 == root) = true
    · have eqRoot : entry.1 = root := beq_iff_eq.mp hq
      have hp : (entry.1 != child) = true := by
        have neChild : entry.1 ≠ child := fun h => distinct (eqRoot.symm.trans h)
        simpa using neChild
      simp [hq, hp]
    · simp [hq]
  have childNeRoot : child ≠ root := Ne.symm distinct
  simp [ProtectedTags.get, ProtectedTags.insert, Array.find?_push, childNeRoot, filtered]

#print axioms insert_preserves_other
end DuplicatePrefix.ProtectedTagsFacts
