import duplicate_prefix.GeneralBorrowFreshModify
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowHomogeneousFullModify
open Miri.ABI Miri.DataStructures
open RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Exact state of the actual modifier on a full positive homogeneous range. -/
theorem state {α : Type} [DecidableEq α] (capacity : UInt64) (nonzero : capacity≠0) (value : α) (modify : α→α) :
    ((homogeneous capacity value).modifyRange Size.ZERO (Size.ofBytes capacity) (fun _ old=>modify old)).state=
      homogeneous capacity (modify value) := by
  have well : (homogeneous capacity value).WellFormed := by simp [homogeneous,DedupRangeMap.WellFormed,UInt64.pos_iff_ne_zero.mpr nonzero]
  have bounds : (0:UInt64).toNat+capacity.toNat≤(homogeneous capacity value).size.bytes.toNat := by
    simp [homogeneous,DedupRangeMap.size,Size.ofBytes]
  rw [GeneralBorrowFreshModify.state_exact (homogeneous capacity value) Size.ZERO (Size.ofBytes capacity) (fun _ old=>modify old) well bounds,
    RangeMapNonempty.iter_mut_homogeneous_full capacity value nonzero]
  simp [GeneralBorrowFreshModify.atPosition,homogeneous]
end DuplicatePrefix.GeneralBorrowHomogeneousFullModify
