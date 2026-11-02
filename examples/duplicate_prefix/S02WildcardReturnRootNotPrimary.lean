import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags

namespace DuplicatePrefix.S02WildcardReturnRootNotPrimary
open Miri Miri.TreeBorrows
set_option autoImplicit false

/-- The fresh wildcard return child is appended after an existing wildcard
root, so it is not the primary root used by the final Return rule. -/
theorem after_push (before after : BorrowTree) (child : UniIndex)
    (nonempty : 0 < before.roots.size)
    (roots : after.roots = before.roots.push child)
    (distinct : after.roots.toList.Nodup) :
    ∀ valid : 0 < after.roots.size, after.roots[0] ≠ child := by
  intro valid same
  have old : before.roots[0]'nonempty = child := by
    simpa only [roots,Array.getElem_push_lt nonempty] using same
  have member : child ∈ before.roots.toList := by
    rw [←old]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem nonempty)
  rw [roots,Array.toList_push,List.nodup_append] at distinct
  exact distinct.2.2 child member child (by simp) rfl

end DuplicatePrefix.S02WildcardReturnRootNotPrimary

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnRootNotPrimary.after_push) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard root order dependency {dependency}"
