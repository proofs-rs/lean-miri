import duplicate_prefix.DuplicatePrefixSliceStorage
import duplicate_prefix.ProvenanceCopy
import duplicate_prefix.CanonicalCopyBound
import duplicate_prefix.PositiveRootCopyBounds
import Miri.TreeBorrows.TreeState
namespace DuplicatePrefix.GeneralBorrowRawSliceBytes
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Count-independent initial bytes of a positive mutable u8 slice. `slice`
states ordinary initialized-value/mask/bounds conditions; `storage` and
`provenance` state allocation-representation consistency; `mutable` is the
allocation write permission. `storageFits` is an explicit numeric resource
margin of the current copy backend, not claimed to follow from slice validity.
Borrow ownership, caller ABI/configuration and external metadata are separate.
No machine trace or successful operation appears in this record. -/
structure Data (allocation : Allocation Provenance BorrowTree) (offset len : UInt64) : Prop where
  slice : DuplicatePrefixSliceStorage.Positive allocation.initializationMask allocation.byteSize.bytes offset len
  storage : allocation.len = allocation.byteSize.bytes.toNat
  provenance : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len
  mutable : allocation.mutability = .Mut
  storageFits : allocation.len+64 < 18446744073709551616

/-- Borrow-tree metadata replacement preserves the initial byte packet;
this connects exact setExtra ledgers without a future-storage premise. -/
theorem Data.set_extra {allocation : Allocation Provenance BorrowTree} {offset len : UInt64}
    (data : Data allocation offset len) (tree : BorrowTree) :
    Data (allocation.setExtra tree) offset len :=
  ⟨data.slice,data.storage,data.provenance,data.mutable,data.storageFits⟩

/-- Initial physical copy conditions for one accepted count. These constrain
only the SAME original allocation and arithmetic, never an execution outcome. -/
structure ForCount (allocation : Allocation Provenance BorrowTree) (offset len count : UInt64) : Prop where
  positive : (0 : UInt64) < count
  within : count ≤ len/2
  sliceBounds : offset.toNat+len.toNat ≤ allocation.byteSize.bytes.toNat
  copyBounds : count.toNat+count.toNat ≤ len.toNat
  sourceBounds : offset.toNat+count.toNat ≤ allocation.byteSize.bytes.toNat
  destinationBounds : (offset+count).toNat+count.toNat ≤ allocation.byteSize.bytes.toNat
  storage : allocation.len = allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed allocation.initializationMask
  maskLen : allocation.initializationMask.len = allocation.byteSize
  initialized : InitMaskCopy.InitializedOn allocation.initializationMask
    (Size.ofBytes offset) (Size.ofBytes (offset+count))
  provenance : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len
  mutable : allocation.mutability = .Mut
  storageFits : allocation.len+64 < 18446744073709551616
  sourceNonwrap : (offset+count).toNat = offset.toNat+count.toNat
  destinationNonwrap : (offset+count+count).toNat = offset.toNat+count.toNat+count.toNat
  sliceNonwrap : (offset+len).toNat = offset.toNat+len.toNat

/-- Whole-slice initialized u8 storage supplies the copy's prefix and every
accepted-count bound. The allocation is unchanged and count is not in Data. -/
theorem Data.for_count {allocation : Allocation Provenance BorrowTree} {offset len : UInt64}
    (data : Data allocation offset len) (count : UInt64)
    (positive : (0 : UInt64) < count) (within : count ≤ len/2) :
    ForCount allocation offset len count := by
  have arithmetic := PositiveRootCopyBounds.guarded len count offset allocation.byteSize.bytes within data.slice.bounds
  have cap := allocation.byteSize.bytes.toNat_lt
  have fullFits : offset.toNat+len.toNat < 2^64 := by have h := data.slice.bounds;omega
  have firstFits : offset.toNat+count.toNat < 2^64 := by omega
  have secondFits : offset.toNat+count.toNat+count.toNat < 2^64 := by omega
  have first : (offset+count).toNat = offset.toNat+count.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt firstFits]
  have second : (offset+count+count).toNat = offset.toNat+count.toNat+count.toNat := by
    rw [UInt64.toNat_add,first,Nat.mod_eq_of_lt secondFits]
  exact {
    positive := positive,within := within,sliceBounds := data.slice.bounds,copyBounds := arithmetic.2.1,
    sourceBounds := arithmetic.2.2.1,destinationBounds := by rw [first];exact arithmetic.2.2.2,
    storage := data.storage,maskValid := data.slice.maskValid,maskLen := data.slice.maskLength,
    initialized := DuplicatePrefixSliceStorage.accepted_initialized _ _ _ _ _ data.slice within,
    provenance := data.provenance,mutable := data.mutable,storageFits := data.storageFits,
    sourceNonwrap := first,destinationNonwrap := second,
    sliceNonwrap := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits] }

/-- The fixed 64-bit configuration maximum follows from the half-length guard;
there is no extra count-dependent resource/configuration premise. -/
theorem ForCount.bounded {allocation : Allocation Provenance BorrowTree} {offset len count : UInt64}
    (data : ForCount allocation offset len count) (options : EvalConfigurationCore.Options)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes :=
  CanonicalCopyBound.guarded options () (remaining+1) span len count data.within
end DuplicatePrefix.GeneralBorrowRawSliceBytes
