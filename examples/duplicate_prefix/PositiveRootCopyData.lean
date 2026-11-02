import duplicate_prefix.PositiveRootSuccessProfile
import duplicate_prefix.PositiveRootCopyBounds
import duplicate_prefix.CopyRootGuardBody

namespace DuplicatePrefix.PositiveRootCopyData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

private theorem initialized_restrict (mask : InitMask) (start finish whole : Size)
    (initialized : InitMaskCopy.InitializedOn mask start whole)
    (bound : finish.bytes.toNat ≤ whole.bytes.toNat) :
    InitMaskCopy.InitializedOn mask start finish := by
  cases blocks : mask.blocks with
  | Lazy state => simpa only [InitMaskCopy.InitializedOn,blocks] using initialized
  | Materialized materialized =>
    simp only [InitMaskCopy.InitializedOn,blocks] at initialized ⊢
    intro block valid bit small lower upper
    exact initialized block valid bit small lower (Nat.lt_of_lt_of_le upper bound)

private theorem prefix_bounds (offset len count capacity : UInt64)
    (within : count ≤ len/2) (bounds : offset.toNat+len.toNat ≤ capacity.toNat) :
    count.toNat+count.toNat ≤ len.toNat ∧ (offset+count).toNat ≤ (offset+len).toNat := by
  have guarded := PositiveRootCopyBounds.guarded len count offset capacity within bounds
  have capacityFits : capacity.toNat < 2^64 := UInt64.toNat_lt_size capacity
  have wholeFits : offset.toNat+len.toNat < 2^64 := by omega
  have prefixFits : offset.toNat+count.toNat < 2^64 := by omega
  refine ⟨guarded.2.1,?_⟩
  simp only [UInt64.toNat_add,Nat.mod_eq_of_lt wholeFits,Nat.mod_eq_of_lt prefixFits]
  omega

/-- Recover the copy's allocation/data contract from the preceding root trace.
Initialization is required for the original slice; the guarded prefix is derived.
The count limit is explicit fixed-configuration data. No operation status is an input. -/
noncomputable def data
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (thread : ThreadRecord) (tags : Fin 6 → BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base capacity offset len count : UInt64)
    (post : PositiveRootSuccessProfile.MachineShape options remaining span before machine tracker thread tags id entry capacity offset len)
    (positive : (0 : UInt64) < count) (within : count ≤ len/2)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len)))
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (storageFits : entry.allocation.len+64 < 18446744073709551616)
    (mutable : entry.allocation.mutability = .Mut)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (distinct : Function.Injective tags)
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    CopyRootGuardBody.CopyData options remaining span machine tracker
      (Scalar.fromPointer config.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset))))
      (Scalar.fromPointer config.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))) count := by
  have arithmetic := prefix_bounds offset len count entry.allocation.byteSize.bytes within bounds
  exact {
    id := id,tag := tags 5,tags := tags,base := base,offset := offset,sliceLen := len,kind := entry.kind
    allocation := entry.allocation.setExtra (NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside capacity offset (offset+len)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)))
    positive := positive,sliceBounds := bounds,copyBounds := arithmetic.1,storage := storage
    maskValid := maskValid,maskLen := maskLength
    initialized := initialized_restrict entry.allocation.initializationMask (Size.ofBytes offset)
      (Size.ofBytes (offset+count)) (Size.ofBytes (offset+len)) initialized arithmetic.2
    valid := provenance,storageFits := storageFits,mutable := mutable
    extras := by rw [post.extras]; exact extras
    live := post.buffer
    cached := by rw [post.addresses]; exact cached
    distinct := distinct,tagAt := rfl
    tree := by
      change NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside capacity offset (offset+len)
        BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false)) =
        NestedBorrowAccess.nestedTree tags (BorrowRangeAccess.partitionWithInside entry.allocation.byteSize.bytes offset (offset+len)
          BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
      rw [allocationSize]
      rfl
    protectionMask := post.mask,bounded := bounded,source := rfl
    destination := by rw [UInt64.add_assoc] }

end DuplicatePrefix.PositiveRootCopyData
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PositiveRootCopyData.data) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved accepted copy-data dependency {dependency}"
