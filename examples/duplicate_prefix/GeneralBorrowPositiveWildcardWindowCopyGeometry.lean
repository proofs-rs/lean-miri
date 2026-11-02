import duplicate_prefix.GeneralBorrowPositiveWildcardWindowLayout
import duplicate_prefix.PositiveRootCopyBounds

namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowCopyGeometry
open Miri.ABI Miri.Memory
open GeneralBorrowPositiveWildcardWindowLayout
set_option maxHeartbeats 2000000

/-- The actual add/copy interfaces use the allocation's cached base and a
separate slice offset. These endpoints remain allocation-relative; neither
pointer addition nor the copy requires rebasing the allocation to its slice. -/
theorem endpoints (s : GeneralBorrowPositiveWildcardWindowLayout.Layout) (count : UInt64) (within : count≤s.len/2) :
    (s.sliceOffset+count).toNat=s.sliceOffset.toNat+count.toNat ∧
    (s.sliceOffset+count+count).toNat=s.sliceOffset.toNat+count.toNat+count.toNat ∧
    (s.allocationBase+s.sliceOffset+count).toNat=
      s.allocationBase.toNat+s.sliceOffset.toNat+count.toNat ∧
    (s.allocationBase+s.sliceOffset+count)-s.allocationBase=s.sliceOffset+count ∧
    s.allocationBase+s.sliceOffset+count=s.allocationBase+(s.sliceOffset+count) ∧
    s.sliceOffset.toNat+count.toNat+count.toNat≤s.capacity.toNat := by
  have bounds:=PositiveRootCopyBounds.guarded s.len count s.sliceOffset s.capacity within s.bounded
  have cap : s.capacity.toNat<2^64 := UInt64.toNat_lt_size s.capacity
  have addr:=s.addressFits
  have first : (s.sliceOffset+count).toNat=s.sliceOffset.toNat+count.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : s.sliceOffset.toNat+count.toNat<2^64)]
  have second : (s.sliceOffset+count+count).toNat=s.sliceOffset.toNat+count.toNat+count.toNat := by
    rw [UInt64.toNat_add,first,Nat.mod_eq_of_lt (by omega : s.sliceOffset.toNat+count.toNat+count.toNat<2^64)]
  have start : (s.allocationBase+s.sliceOffset).toNat=s.allocationBase.toNat+s.sliceOffset.toNat := address_nat s
  have added : (s.allocationBase+s.sliceOffset+count).toNat=
      s.allocationBase.toNat+s.sliceOffset.toNat+count.toNat := by
    rw [UInt64.toNat_add,start,Nat.mod_eq_of_lt (by omega : s.allocationBase.toNat+s.sliceOffset.toNat+count.toNat<2^64)]
  refine ⟨first,second,added,?_,UInt64.add_assoc ..,bounds.2.2.2⟩
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [added];omega)),added,first]
  omega

/-- Both real memory-access bounds checks and the real checked source endpoint
follow from the slice guard. Initialization and permission inputs can therefore
remain confined to the source interval, as in `CopyRootGuardBody.CopyData`. -/
theorem checks (s : GeneralBorrowPositiveWildcardWindowLayout.Layout) (count : UInt64) (within : count≤s.len/2)
    (target : PointerArithmetic) (id : AllocId) :
    checkedBounds target id (Size.ofBytes s.capacity) (Size.ofBytes s.sliceOffset)
      (Int.ofNat count.toNat) .memoryAccess=.ok () ∧
    checkedBounds target id (Size.ofBytes s.capacity) (Size.ofBytes (s.sliceOffset+count))
      (Int.ofNat count.toNat) .memoryAccess=.ok () ∧
    (allocRange (Size.ofBytes s.sliceOffset) (Size.ofBytes count)).endExclusive=
      .ok (Size.ofBytes (s.sliceOffset+count)) := by
  have bounds:=PositiveRootCopyBounds.guarded s.len count s.sliceOffset s.capacity within s.bounded
  have cap : s.capacity.toNat<2^64 := UInt64.toNat_lt_size s.capacity
  have endpoint:=(endpoints s count within).1
  refine ⟨?_,?_,source_end (Size.ofBytes s.sliceOffset) count (by change s.sliceOffset.toNat+count.toNat<2^64;omega)⟩
  · exact checkedBounds_ok target id (Size.ofBytes s.capacity) (Size.ofBytes s.sliceOffset) count.toNat .memoryAccess bounds.1 bounds.2.2.1
  · apply checkedBounds_ok
    · exact bounds.1
    · change (s.sliceOffset+count).toNat+count.toNat≤s.capacity.toNat
      rw [endpoint]
      exact bounds.2.2.2

end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowCopyGeometry
