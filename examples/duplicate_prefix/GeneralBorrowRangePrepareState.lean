import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralRangeMapSafety
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowRangePrepareState
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- The real range preparation may merge equal adjacent rows; retain its
actual state rather than assuming partition representation is unchanged. -/
def prepared (tree : BorrowTree) (offset len : Size) : BorrowTree :=
  {tree with locations:=(tree.locations.iterMut offset len).state}
theorem state (tree : BorrowTree) (offset len : Size)
    (initial : GeneralBorrowStructuralHistoryState.State tree)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    GeneralBorrowStructuralHistoryState.State (prepared tree offset len) ∧
      (prepared tree offset len).locations.size=tree.locations.size := by
  have good:=GeneralRangeMapSafety.iter_mut (fun _ : LocationTree=>True) tree.locations offset len initial.well
    (by intro position valid;trivial) bounds
  exact ⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ initial.toGraphState,good.wellFormed⟩,
    congrArg Size.ofBytes good.capacity⟩
theorem every (tree : BorrowTree) (offset len : Size) (predicate : LocationTree→Prop)
    (well : tree.locations.WellFormed) (initial : GeneralRangeMapState.Every predicate tree.locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    GeneralRangeMapState.Every predicate (prepared tree offset len).locations :=
  (GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well initial bounds).every
theorem clean (tree : BorrowTree) (offset len : Size) (well : tree.locations.WellFormed)
    (initial : GeneralBorrowGcVacantClean.VacantClean tree)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    GeneralBorrowGcVacantClean.VacantClean (prepared tree offset len) := by
  intro query vacant
  exact every tree offset len (fun location=>location.perms.get query=none) well (initial query vacant) bounds
end DuplicatePrefix.GeneralBorrowRangePrepareState
