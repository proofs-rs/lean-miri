import duplicate_prefix.GeneralBorrowPrimaryWitnessVisibility
import duplicate_prefix.GeneralBorrowParentTagInvariant
namespace DuplicatePrefix.GeneralBorrowFreshCutoffClosure
open Miri Miri.Memory Miri.TreeBorrows
open GeneralBorrowPrimaryWitnessVisibility
set_option autoImplicit false
/-- A global tag bound is one sufficient static condition for closure at a
fixed cutoff. No parent-tag order or interpreter outcome is needed. -/
theorem closed_of_tag_bound (tree : BorrowTree) (maximum : BorTag)
    (bound : ∀ index node, tree.nodes.get index = some node → node.tag.value ≤ maximum.value) :
    CutoffClosed tree (some maximum) := by
  intro witness node present below
  exact of_tag_bound tree maximum witness bound

/-- At the allocator's current fresh cutoff, RuntimeFacts alone supply closure.
This does not cover an OLD selected-root cutoff and is not a claim that RuntimeFacts
implies global ParentTagOrder. -/
theorem closed_of_runtime_fresh (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) :
    CutoffClosed tree (some global.nextPointerTag) := by
  apply closed_of_tag_bound
  intro index node present
  have bound := GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime index node present
  exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp bound))
end DuplicatePrefix.GeneralBorrowFreshCutoffClosure
