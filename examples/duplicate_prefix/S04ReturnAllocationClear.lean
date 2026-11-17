import duplicate_prefix.S04ReturnProvenanceClear
import duplicate_prefix.AllocationCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnAllocationClear
open Miri.ABI Miri.Memory
set_option autoImplicit false
open Lean Elab in
elab "clear_alloc_mk" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".Miri.Memory.Allocation.mk" then some name else none
  let [name] := names | throwError "expected allocation constructor"
  return mkConst name

theorem clear_exists {Extra : Type} (allocation : Allocation Provenance Extra)
    (capacity offset : UInt64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat+1≤capacity.toNat)
    (pointerBounds : ∀ entry ∈ allocation.provenanceMap.ptrs,
      entry.1.bytes.toNat+8≤allocation.len) :
    ∃ updated, Allocation.clearProvenance (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Size.ofBytes 8) allocation = .ok () updated ∧
      updated.len = allocation.len ∧ updated.byteSize = allocation.byteSize ∧
      updated.mutability = allocation.mutability ∧ updated.extra = allocation.extra ∧
      updated.initializationMask = allocation.initializationMask ∧
      ∀ layout, Allocation.readScalar updated layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false =
        Allocation.readScalar allocation layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false := by
  have fits := capacity.toNat_lt
  have endNat : (offset+1).toNat=offset.toNat+1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using (show offset.toNat+1<2^64 by omega))
  have ordered : offset≤offset+1 := UInt64.le_iff_toNat_le.mpr (by omega)
  have bounded : offset+1≤capacity := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨bytes,slice,_⟩ := AllocationCopy.raw_slice_exists allocation _ _
    (by simpa [size,Size.ofBytes] using storage) endpoint ordered (by simpa [size,Size.ofBytes] using bounded)
  cases allocation
  rename_i raw allocationSize oldProvenance mask align mutable extra native
  simp only [Allocation.len,Allocation.byteSize,Allocation.provenanceMap] at *
  subst allocationSize
  obtain ⟨provenance,clear⟩ := ProvenanceCopy.clear_exists oldProvenance _ _ raw endpoint pointerBounds (by omega)
  refine ⟨clear_alloc_mk raw (Size.ofBytes capacity) provenance mask align mutable extra native,
    ?_,rfl,rfl,rfl,rfl,rfl,?_⟩
  · unfold Allocation.clearProvenance
    unfold Allocation.getBytesUnchecked at slice
    erw [slice]
    simp only [Bind.bind,Pure.pure,Id.instMonad,Id.run]
    erw [clear]
  · intro layout
    unfold Allocation.readScalar
    rfl
end DuplicatePrefix.S04ReturnAllocationClear
