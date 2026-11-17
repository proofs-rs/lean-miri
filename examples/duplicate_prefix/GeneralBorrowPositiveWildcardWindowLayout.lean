import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowLayout
open Miri.ABI Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Allocation addresses remain allocation-relative. The slice is a distinct
bounded positive window; its pointer address is computed from the real base. -/
structure Layout where
  allocationBase : UInt64
  capacity : UInt64
  sliceOffset : UInt64
  len : UInt64
  baseNonzero : allocationBase≠0
  positive : 0<len
  bounded : sliceOffset.toNat+len.toNat≤capacity.toNat
  addressFits : allocationBase.toNat+capacity.toNat<2^64

def address (s : Layout) : UInt64:=s.allocationBase+s.sliceOffset

theorem offset_lt (s : Layout) : s.sliceOffset.toNat<s.capacity.toNat := by
  have positive:=UInt64.lt_iff_toNat_lt.mp s.positive
  have bounded:=s.bounded
  simp only [UInt64.toNat_zero] at positive
  omega

theorem address_nat (s : Layout) : (address s).toNat=s.allocationBase.toNat+s.sliceOffset.toNat := by
  have bounded:=offset_lt s
  have fits:=s.addressFits
  change (s.allocationBase+s.sliceOffset).toNat=_
  rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : s.allocationBase.toNat+s.sliceOffset.toNat<2^64)]

theorem relative (s : Layout) : address s-s.allocationBase=s.sliceOffset := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [address_nat s];omega)),address_nat s]
  omega

theorem address_nonzero (s : Layout) : address s≠0 := by
  intro zero
  have positive:=UInt64.pos_iff_ne_zero.mpr s.baseNonzero
  have value:=UInt64.lt_iff_toNat_lt.mp positive
  have actual:=address_nat s
  rw [zero] at actual
  simp only [UInt64.toNat_zero] at actual value
  omega

theorem copy_bounds (s : Layout) (count : UInt64) (within : count≤s.len/2) :
    s.sliceOffset.toNat+2*count.toNat≤s.capacity.toNat := by
  have countBound:=UInt64.le_iff_toNat_le.mp within
  have bounded:=s.bounded
  change count.toNat≤s.len.toNat/2 at countBound
  omega
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowLayout
