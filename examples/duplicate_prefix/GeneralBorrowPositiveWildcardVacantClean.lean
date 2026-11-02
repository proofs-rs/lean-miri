import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardVacantClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowGcVacantClean GeneralBorrowFreshFutureClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Positive wildcard-root materialization preserves allocation-wide vacant
permission cleanliness. No constructor-success premise is needed. -/
theorem preserves (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (outside : Permission) (sifa : IdempotentForeignAccess) (inside : LocationState) (offset len : UInt64)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : VacantClean tree) :
    VacantClean (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len) := by
  intro query vacant
  have different : query ≠ index := by
    intro same
    rw [same] at vacant
    have present := (GeneralBorrowPositiveWildcardConstructor.geometry tree mapping index tag outside sifa inside offset len).2
    rw [show (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag outside sifa inside offset len).nodeAt index = none from vacant] at present
    cases present
  have initialVacant : tree.nodes.get query = none := by
    change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).get query = none at vacant
    rw [GeneralBorrowFreshLocation.get_other _ index query _ different] at vacant
    exact vacant
  exact GeneralBorrowFreshFutureClean.modified tree.locations index query (Size.ofBytes offset) (Size.ofBytes len) inside
    different well bounds (clean query initialVacant)
end DuplicatePrefix.GeneralBorrowPositiveWildcardVacantClean
