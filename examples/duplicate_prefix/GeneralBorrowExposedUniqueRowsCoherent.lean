import duplicate_prefix.GeneralBorrowNormalExposureTodo
import duplicate_prefix.GeneralBorrowWildcardLeaf
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRowsCoherent
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Hidden-node permission transitions and real table changes leave coherent
counters intact when every exposed node retains its exact Unique row. -/
theorem frame (tree : BorrowTree) (before after : LocationTree) (oldTable newTable : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree before oldTable)
    (cache : after.exposedCache=before.exposedCache)
    (unique : ∀ index node,tree.nodeAt index=some node → node.isExposed=true →
      before.perms.get index=some GeneralBorrowWildcardLeaf.unique ∧ after.perms.get index=some GeneralBorrowWildcardLeaf.unique) :
    GeneralBorrowExposureCardinality.LocationCoherent tree after newTable := by
  intro query kind
  rw [cache,coherent query kind]
  apply congrArg UInt16.ofNat
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  cases flag : row.2.isExposed with
  | false => simp only [GeneralBorrowExposureCardinality.contributes,flag,Bool.false_and]
  | true =>
    obtain ⟨old,new⟩ := unique row.1 row.2 present flag
    simp only [GeneralBorrowExposureCardinality.contributes,GeneralBorrowExposureCardinality.effective,old,new,
      GeneralBorrowWildcardLeaf.unique,Option.getD_some,Permission.strongestAllowedLocalAccess]
end DuplicatePrefix.GeneralBorrowExposedUniqueRowsCoherent
