import duplicate_prefix.GeneralBorrowRawSliceBytes

namespace DuplicatePrefix.OrdinaryPhysicalValidity
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false

/-- Allocation-representation consistency, separate from reference ownership.
No address cache, tag ordering, permission profile or execution is mentioned. -/
structure Storage (allocation : Allocation Provenance BorrowTree) : Prop where
  byteLength : allocation.len = allocation.byteSize.bytes.toNat
  maskLength : allocation.initializationMask.len = allocation.byteSize
  maskCapacity : InitMaskCopy.WellFormed allocation.initializationMask
  provenance : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len

/-- The actual initialization bit of byte `index`, without a wrapped interval
endpoint. A lazy mask has the same bit at every byte. The index bound belongs
to the containing physical window. -/
def ByteInitialized (mask : InitMask) (index : Nat) : Prop :=
  match mask.blocks with
  | .Lazy value => value = true
  | .Materialized blocks => ∃ h : index / 64 < blocks.blocks.size,
      Nat.testBit (blocks.blocks[index / 64]'h).toNat (index % 64) = true

/-- Physical value component of a positive mutable u8 slice. Every u8 bit
pattern is valid, so initialized bytes, a signed-size bound and containment
are the value conditions. Writability is an allocation property. This is NOT
complete reference validity: provenance resolution, nonnull/alignment and
Tree Borrows ownership remain separate and unproved here.

This component follows the size/access checks in pinned validity.rs
check_safe_pointer and the primitive initialized-scalar check. It makes no
claim that shallow reference validation itself recursively checks all bytes. -/
structure MutU8Slice (allocation : Allocation Provenance BorrowTree)
    (offset len : UInt64) : Prop where
  storage : Storage allocation
  nonempty : 0 < len.toNat
  signedSize : len.toNat < 9223372036854775808
  contained : offset.toNat + len.toNat ≤ allocation.byteSize.bytes.toNat
  writable : allocation.mutability = .Mut
  values : ∀ index, offset.toNat ≤ index → index < offset.toNat + len.toNat →
    ByteInitialized allocation.initializationMask index

/-- Writable physical bool destination. Its previous byte need not be a valid
bool or even initialized: the call overwrites it. Typed place layout, pointer
resolution and borrow authorization are deliberately not certified by this
physical component. No copy-backend resource margin is included. -/
structure BoolDestination (allocation : Allocation Provenance BorrowTree)
    (offset : UInt64) : Prop where
  storage : Storage allocation
  contained : offset.toNat + 1 ≤ allocation.byteSize.bytes.toNat
  writable : allocation.mutability = .Mut

/-- Raw byte initialization covers the exact existing mask interval, using
containment to justify UInt64 addition rather than assuming a wrapped end. -/
theorem initialized_interval {mask : InitMask} {capacity offset len : UInt64}
    (positive : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (values : ∀ index, offset.toNat ≤ index → index < offset.toNat + len.toNat →
      ByteInitialized mask index) :
    InitMaskCopy.InitializedOn mask (Size.ofBytes offset) (Size.ofBytes (offset + len)) := by
  have fits : offset.toNat + len.toNat < 2^64 := Nat.lt_of_le_of_lt bounds capacity.toNat_lt
  have endpoint : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  cases h : mask.blocks with
  | Lazy flag =>
    have value := values offset.toNat (by omega) (by omega)
    simpa [ByteInitialized, InitMaskCopy.InitializedOn, h] using value
  | Materialized blocks =>
    simp only [InitMaskCopy.InitializedOn, h, InitMaskCopy.MaterializedInitializedOn]
    intro block hb bit small lower upper
    change offset.toNat ≤ block * 64 + bit at lower
    change block * 64 + bit < (offset + len).toNat at upper
    rw [endpoint] at upper
    have value := values (block * 64 + bit) lower upper
    simp only [ByteInitialized, h] at value
    obtain ⟨hv, value⟩ := value
    have div : (block * 64 + bit) / 64 = block := by omega
    have mod : (block * 64 + bit) % 64 = bit := by omega
    simpa only [div, mod] using value

/-- Exact coverage of the existing positive storage/bounds predicate. Borrow
capabilities and normalization of physical pointers are not conclusions. -/
theorem MutU8Slice.slice_storage {allocation : Allocation Provenance BorrowTree}
    {offset len : UInt64} (input : MutU8Slice allocation offset len) :
    DuplicatePrefixSliceStorage.Positive allocation.initializationMask
      allocation.byteSize.bytes offset len := {
  positive := input.nonempty
  signedSize := input.signedSize
  bounds := input.contained
  maskValid := input.storage.maskCapacity
  maskLength := by simpa [Size.ofBytes] using input.storage.maskLength
  initialized := initialized_interval input.nonempty input.contained input.values }

/-- Resource separation is explicit: the backend's +64 headroom is supplied
separately and is not smuggled into the physical value domain. -/
theorem MutU8Slice.copy_data {allocation : Allocation Provenance BorrowTree}
    {offset len : UInt64} (input : MutU8Slice allocation offset len)
    (backendRoom : allocation.len + 64 < 18446744073709551616) :
    GeneralBorrowRawSliceBytes.Data allocation offset len :=
  ⟨input.slice_storage, input.storage.byteLength, input.storage.provenance,
    input.writable, backendRoom⟩

/-- Every accepted copy gets actual bounds and initialized source bytes from
one count-independent physical value domain. No successful operation appears
in the assumptions. -/
theorem MutU8Slice.accepted_copy {allocation : Allocation Provenance BorrowTree}
    {offset len : UInt64} (input : MutU8Slice allocation offset len)
    (backendRoom : allocation.len + 64 < 18446744073709551616)
    (count : UInt64) (positive : (0 : UInt64) < count) (within : count ≤ len / 2) :
    GeneralBorrowRawSliceBytes.ForCount allocation offset len count :=
  (input.copy_data backendRoom).for_count count positive within

/-- The physical destination is an actual in-allocation byte and its endpoint
cannot wrap, including a destination embedded in the source allocation. -/
theorem BoolDestination.bounds {allocation : Allocation Provenance BorrowTree}
    {offset : UInt64} (input : BoolDestination allocation offset) :
    offset.toNat < allocation.byteSize.bytes.toNat ∧
      (offset + 1).toNat = offset.toNat + 1 := by
  have bounds := input.contained
  have cap := allocation.byteSize.bytes.toNat_lt
  constructor
  · omega
  · rw [UInt64.toNat_add]
    change (offset.toNat + 1) % 2^64 = offset.toNat + 1
    exact Nat.mod_eq_of_lt (by omega)

end DuplicatePrefix.OrdinaryPhysicalValidity
