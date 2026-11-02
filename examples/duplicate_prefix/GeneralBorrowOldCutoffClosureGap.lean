import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility
import duplicate_prefix.PrimaryWitnessCountermodel
namespace DuplicatePrefix.GeneralBorrowOldCutoffClosureGap
open Miri Miri.Memory Miri.TreeBorrows
open GeneralBorrowPrimaryWitnessVisibility GeneralBorrowExposedNonleafPrimaryPath
open PrimaryWitnessCountermodel
/-- The existing diagnostic fails closure at its actual OLD selected-root
cutoff5: exposed tag2 is below Disabled ancestor tag9. This proves neither
valid Rust reachability nor a whole-call counterexample. -/
theorem old_cutoff_not_closed : ¬CutoffClosed tree (some (tag 5)) := by
  intro closed
  have visible := closed (ix 2) n2 rfl (by decide)
  have path : Path tree (ix 1) (ix 2) := .step (.refl (ix 1) n1 rfl) n2 rfl rfl
  have impossible := visible (ix 1) n1 rfl path
  have above : DuplicatePrefixCallbackAuthorization.aboveMaximum n1 (some (tag 5)) = true := by decide
  rw [above] at impossible
  cases impossible
end DuplicatePrefix.GeneralBorrowOldCutoffClosureGap
