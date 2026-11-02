import duplicate_prefix.GeneralBorrowPositiveWildcardPartitionArgumentCopy
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
import duplicate_prefix.GeneralBorrowRangePrepareState
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionVacantClean
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual partition preparation and wildcard root materialization preserve
vacancy cleanliness across the whole allocation. -/
theorem preserves (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (len : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : (0 : UInt64).toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowPositiveWildcardPartitionArgumentCopy.finalTree tree tracker len) := by
  let prepared:=GeneralBorrowRangePrepareState.prepared tree Size.ZERO (Size.ofBytes len)
  have good:=GeneralRangeMapSafety.iter_mut (fun _ : LocationTree=>True) tree.locations Size.ZERO (Size.ofBytes len) well
    (by intro position valid;trivial) bounds
  have nextBounds : (0 : UInt64).toNat+len.toNat≤prepared.locations.size.bytes.toNat := by
    change (0 : UInt64).toNat+len.toNat≤(tree.locations.iterMut Size.ZERO (Size.ofBytes len)).state.size.bytes.toNat
    rw [good.capacity]
    exact bounds
  exact GeneralBorrowPositiveWildcardVacantClean.preserves prepared _ _ _ _ _ _ _ _ good.wellFormed nextBounds
    (GeneralBorrowRangePrepareState.clean tree Size.ZERO (Size.ofBytes len) well clean bounds)
end DuplicatePrefix.GeneralBorrowPositiveWildcardPartitionVacantClean
