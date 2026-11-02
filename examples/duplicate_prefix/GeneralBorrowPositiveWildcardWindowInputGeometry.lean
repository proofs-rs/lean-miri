import duplicate_prefix.GeneralBorrowPositiveWildcardWindowOriginalInput
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowInputGeometry
open Miri Miri.ABI Miri.Memory
variable [area : GeneralBorrowExposedKnownRootState.Scope]
def window (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : GeneralBorrowPositiveWildcardWindowLayout.Layout :=
  ⟨s.base,s.capacity,s.offset,s.len,s.nonzero,s.positive,s.bounds,s.addressFits⟩
theorem nonzero (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : s.base+s.offset≠0 :=
  GeneralBorrowPositiveWildcardWindowLayout.address_nonzero (window s)
theorem pointerFits (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : s.base.toNat+s.offset.toNat+s.len.toNat<2^64 := by
  have fits:=s.addressFits
  have bounds:=s.bounds
  omega
theorem byteBounds (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : s.offset.toNat+s.len.toNat≤s.entry.allocation.byteSize.bytes.toNat := by
  rw [s.bufferSize]
  exact s.bounds
theorem treeBounds (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : s.offset.toNat+s.len.toNat≤s.entry.allocation.extra.locations.size.bytes.toNat := by
  rw [s.allocationCapacity]
  exact s.bounds
theorem positiveEnd (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) : s.offset.toNat<(s.offset+s.len).toNat := by
  have positive:=UInt64.lt_iff_toNat_lt.mp s.positive
  have bounds:=s.bounds
  have cap:=s.capacity.toNat_lt
  rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  simp only [UInt64.toNat_zero] at positive
  omega
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowInputGeometry
