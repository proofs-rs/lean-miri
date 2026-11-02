import duplicate_prefix.GeneralBorrowFreshRootScopedSource
import duplicate_prefix.GeneralBorrowReadRowRange
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedReadRow
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowFreshRootSupportCutoff
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Read-only selected Normal, with BOTH bounded other-root callbacks. -/
structure Row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : BorTag) where
  base : GeneralBorrowReadRowNormal.ReadRow tree location protections (some source) (some selected) (some maximum)
  exposed : ExposedBound tree maximum
  callbacks : ∀ position,(valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
    ∃ support,SupportBound tree maximum support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Read support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Write support

structure Positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64) where
  base : GeneralBorrowReadRowRange.Positive tree protections source selected (some maximum) offset len
  rows : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (Row tree location protections source selected maximum))
    offset (offset+len) tree.locations

theorem of_positive (tree : BorrowTree) (protections : ProtectedTags) (source selected : UniIndex)
    (maximum : BorTag) (offset len : UInt64)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree protections source selected maximum offset len) :
    Nonempty (Positive tree protections source selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowReadRowRange.of_positive tree protections source selected (some maximum) offset len old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonzero start stop
  obtain ⟨row⟩ := old.rows position valid nonzero start stop
  exact ⟨⟨GeneralBorrowReadRowNormal.of_row tree _ protections _ _ _ row.base,row.exposed,row.callbacks⟩⟩

theorem source (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (parent selected : UniIndex) (maximum : BorTag) (row : Row tree location protections parent selected maximum) :
    GeneralBorrowFreshRootScopedSource.Source tree location protections parent selected maximum :=
  ⟨GeneralBorrowCallbackSource.of_read_row tree location protections parent selected (some maximum) row.base,row.exposed,row.callbacks⟩

theorem locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (source selected : UniIndex) (maximum : BorTag)
    (row : Row tree location protections source selected maximum) :
    Nonempty (Row {tree with locations := locations} location protections source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowReadRowRange.row_locations tree locations location protections source selected (some maximum) ⟨row.base⟩
  refine ⟨⟨base,row.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := row.callbacks position valid different
  exact ⟨support,bounded,
    GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections _ _ _ _ _ read,
    GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections _ _ _ _ _ write⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedReadRow
