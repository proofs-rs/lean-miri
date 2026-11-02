import duplicate_prefix.DuplicatePrefixBorrowContract

namespace DuplicatePrefix.S02SeparateDestinationRuntimeRebase
open Miri Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- An unchanged protector table and advanced tag counter preserve runtime facts for an untouched allocation. -/
theorem advance
    (tree : BorrowTree) (before after : GlobalState)
    (facts : DuplicatePrefixBorrowContract.RuntimeFacts tree before)
    (protections : after.protectedTags = before.protectedTags)
    (counter : before.nextPointerTag.value.toNat ≤ after.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree after := by
  refine ⟨?_,?_,facts.possible,?_⟩
  · rw [protections]
    exact facts.formed
  · rw [protections]
    exact facts.coherent
  · constructor
    · intro row member
      have old := facts.below.mapping row member
      omega
    · intro row member
      rw [protections] at member
      have old := facts.below.protectors row member
      omega

end
end DuplicatePrefix.S02SeparateDestinationRuntimeRebase

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationRuntimeRebase.advance) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved runtime rebase dependency {dependency}"
