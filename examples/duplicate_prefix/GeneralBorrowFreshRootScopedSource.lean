import duplicate_prefix.GeneralBorrowCallbackSource
import duplicate_prefix.GeneralBorrowFreshRootScopedRow
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSource
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowFreshRootSupportCutoff
set_option autoImplicit false
/-- Permission-independent constructor source with retained bounded callbacks. -/
structure Source (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : BorTag) : Prop where
  base : GeneralBorrowCallbackSource.Source tree location protections parent selected (some maximum)
  exposed : ExposedBound tree maximum
  callbacks : ∀ position,(valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
    ∃ support,SupportBound tree maximum support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Read support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Write support

theorem of_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : BorTag)
    (row : GeneralBorrowFreshRootScopedRow.Row tree location protections parent selected maximum) :
    Source tree location protections parent selected maximum :=
  ⟨GeneralBorrowCallbackSource.of_row tree location protections parent selected (some maximum) row.base,row.exposed,row.callbacks⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedSource
