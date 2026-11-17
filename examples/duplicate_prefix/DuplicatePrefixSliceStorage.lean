import duplicate_prefix.InitMaskInitializedSubrange
import Miri.Memory.Allocation

namespace DuplicatePrefix.DuplicatePrefixSliceStorage
open Miri Miri.ABI Miri.Memory

set_option autoImplicit false in
/-- Storage part of a valid positive `&mut [u8]`, stated before the call and
independently of count. Resolution, exclusive borrow ownership and caller ABI
are separate obligations. This record is deliberately not called ValidCaller.
All slice bytes are initialized, as required for a slice of u8 values; the
function's weaker accepted-prefix initialization contract remains available. -/
structure Positive (mask : InitMask) (capacity offset len : UInt64) : Prop where
  positive : 0 < len.toNat
  signedSize : len.toNat < 9223372036854775808
  bounds : offset.toNat + len.toNat ≤ capacity.toNat
  maskValid : InitMaskCopy.WellFormed mask
  maskLength : mask.len = Size.ofBytes capacity
  initialized : InitMaskCopy.InitializedOn mask
    (Size.ofBytes offset) (Size.ofBytes (offset + len))

/-- Every accepted copy reads an initialized prefix. This is derived from a
count-independent valid-slice storage condition, not assumed operation success.
The interval endpoint is offset+count, never count. -/
theorem accepted_initialized (mask : InitMask) (capacity offset len count : UInt64)
    (storage : Positive mask capacity offset len) (accepted : count ≤ len / 2) :
    InitMaskCopy.InitializedOn mask (Size.ofBytes offset) (Size.ofBytes (offset + count)) := by
  have countBound : count.toNat ≤ len.toNat := by
    have bound := UInt64.le_iff_toNat_le.mp accepted
    have divided : (len / 2).toNat = len.toNat / 2 := UInt64.toNat_div len 2
    rw [divided] at bound
    omega
  have fullFits : offset.toNat + len.toNat < 2^64 :=
    Nat.lt_of_le_of_lt storage.bounds capacity.toNat_lt
  have prefixFits : offset.toNat + count.toNat < 2^64 := by omega
  apply InitMaskInitializedSubrange.subrange mask
    (Size.ofBytes offset) (Size.ofBytes (offset + len))
    (Size.ofBytes offset) (Size.ofBytes (offset + count)) (Nat.le_refl _) _ storage.initialized
  change (offset + count).toNat ≤ (offset + len).toNat
  rw [UInt64.toNat_add, UInt64.toNat_add,
    Nat.mod_eq_of_lt prefixFits, Nat.mod_eq_of_lt fullFits]
  omega

end DuplicatePrefix.DuplicatePrefixSliceStorage
