import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility
import duplicate_prefix.PrimaryWitnessCountermodel
namespace DuplicatePrefix.GeneralBorrowCutoffClosedStrictness
open Miri Miri.Memory Miri.TreeBorrows
open GeneralBorrowPrimaryWitnessVisibility PrimaryWitnessCountermodel
/-- Static strictness only. This is cutoff10, whereas the original diagnostic
selected root has tag5. Consequently this does NOT demonstrate a larger
RawFnEntry/whole-function input domain respecting Row.cutoff. No valid Rust
history, successful function invocation or reachability is claimed. -/
theorem inverted_closed : CutoffClosed tree (some (tag 10)) ∧
    ¬GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree := by
  constructor
  · intro witness node present below
    apply of_tag_bound
    intro index node found
    rcases lookup_cases index node found with h | h | h | h | h <;>
      rcases h with ⟨rfl,rfl⟩ <;> decide
  · intro ordered
    have bad := ordered (ix 2) n2 rfl (ix 1) n1 rfl rfl
    exact (by decide : ¬n1.tag.value ≤ n2.tag.value) bad
end DuplicatePrefix.GeneralBorrowCutoffClosedStrictness
