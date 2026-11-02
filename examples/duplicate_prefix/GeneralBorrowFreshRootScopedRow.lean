import duplicate_prefix.GeneralBorrowWildcardRootRowPositive
import duplicate_prefix.GeneralBorrowFreshRootPrimaryReadBoth
import duplicate_prefix.GeneralBorrowFreshRootPrimaryWriteBoth
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization GeneralBorrowFreshRootSupportCutoff
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- A raw concrete row with its actual callback supports retained explicitly.
New hidden nodes above the selected-root cutoff are unrestricted outside those
supports. This is current permission data, never a future traversal plan. -/
structure Row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : BorTag) where
  base : DuplicatePrefixBorrowAuthorization.Row tree location protections (some source) (some selected) (some maximum)
  exposed : ExposedBound tree maximum
  callbacks : ∀ position,(valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
    ∃ support, SupportBound tree maximum support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Read support ∧
      Authorization tree location protections tree.roots[position] position (some maximum) .Write support

/-- The fresh constructor's all-old-node highwater bound forms the refined
packet without imposing any ordering among parent and child tags. -/
theorem of_bound (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : BorTag) (bound : GeneralBorrowFreshRootCutoff.Bound tree maximum)
    (base : DuplicatePrefixBorrowAuthorization.Row tree location protections (some source) (some selected) (some maximum)) :
    Nonempty (Row tree location protections source selected maximum) := by
  refine ⟨⟨base,exposed_of_bound tree maximum bound,?_⟩⟩
  intro position valid different
  obtain ⟨support,read,write⟩ := base.callbacks position valid (by simpa using different)
  exact ⟨support,(by intro query node included present;exact bound query node present),read,write⟩

/-- Changing only range segmentation retains the exact saved supports. -/
theorem locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (source selected : UniIndex) (maximum : BorTag)
    (row : Row tree location protections source selected maximum) :
    Nonempty (Row {tree with locations := locations} location protections source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowWildcardRootRowPositive.row_locations tree locations location protections
    (some source) (some selected) (some maximum) row.base
  refine ⟨⟨base,row.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := row.callbacks position valid different
  exact ⟨support,bounded,
    GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections _ _ _ _ _ read,
    GeneralBorrowSnapshotWildcardRangeBoth.authorization_locations tree locations location protections _ _ _ _ _ write⟩

/-- Bounded positive ownership stores the refined callback packet only on
intersecting physical rows. Its ordinary Positive projection is immediate. -/
structure Positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64) where
  base : DuplicatePrefixBorrowAuthorization.Positive tree protections (some source) (some selected) (some maximum) offset len
  rows : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (Row tree location protections source selected maximum))
    offset (offset+len) tree.locations

theorem positive_of_bound (tree : BorrowTree) (protections : ProtectedTags) (source selected : UniIndex)
    (maximum : BorTag) (offset len : UInt64) (bound : GeneralBorrowFreshRootCutoff.Bound tree maximum)
    (base : DuplicatePrefixBorrowAuthorization.Positive tree protections (some source) (some selected) (some maximum) offset len) :
    Nonempty (Positive tree protections source selected maximum offset len) := by
  refine ⟨⟨base,?_⟩⟩
  intro position valid positive start stop
  obtain ⟨row⟩ := base.rows position valid positive start stop
  exact of_bound tree _ protections source selected maximum bound row
end DuplicatePrefix.GeneralBorrowFreshRootScopedRow
