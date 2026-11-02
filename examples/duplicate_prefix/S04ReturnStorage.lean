import duplicate_prefix.DuplicatePrefixReturnPlaceInput
import duplicate_prefix.AllocationCopy
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnStorage
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique helper {suffix}"
elab "target_bytes_return" : term => return mkConst (← sourceName ".Miri.Memory.targetUIntBytes")
elab "return_alloc" : term => return mkConst (← sourceName ".Miri.Memory.Allocation.mk")
theorem bool_encode (layout : TargetDataLayout) (value : Bool) :
    target_bytes_return layout (Size.ofBytes 1) (if value then 1 else 0) =
      Except.ok #[if value then 1 else 0] := by
  cases value <;> unfold_internal ".Miri.Memory.targetUIntBytes" <;>
    simp [Size.ofBytes, bind, Except.bind, pure, Except.pure, Id.run, List.range'_succ,
      List.forIn_cons, List.forIn_nil]

theorem store {Extra : Type} (allocation : Allocation Provenance Extra)
    (layout : TargetDataLayout) (capacity offset : UInt64) (value : Bool)
    (width : layout.pointerWidth.bits = 64)
    (storage : allocation.len = capacity.toNat)
    (size : allocation.byteSize = Size.ofBytes capacity)
    (mutable : allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLength : allocation.initializationMask.len = Size.ofBytes capacity)
    (provenanceValid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (bounds : offset.toNat + 1 ≤ capacity.toNat) :
    ∃ updated, Allocation.writeScalar layout (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Scalar.fromBool value) allocation = .ok () updated ∧
      updated.len = allocation.len ∧ updated.byteSize = allocation.byteSize ∧
      updated.mutability = .Mut ∧ updated.extra = allocation.extra := by
  cases allocation
  rename_i raw allocationSize oldProvenance oldMask align mutability extra native
  simp only [Allocation.len, Allocation.byteSize, Allocation.initializationMask,
    Allocation.provenanceMap] at *
  subst allocationSize
  subst mutability
  let range := allocRange (Size.ofBytes offset) (Size.ofBytes 1)
  let finish := Size.ofBytes (offset + 1)
  have fits := capacity.toNat_lt
  have endNat : (offset + 1).toNat = offset.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_one]; apply Nat.mod_eq_of_lt; omega
  have endpoint : range.endExclusive = .ok finish :=
    DuplicatePrefix.source_end (Size.ofBytes offset) 1 (by simpa [Size.ofBytes] using (show offset.toNat + 1 < 2^64 by omega))
  obtain ⟨mask, maskOk, maskLen, maskWf⟩ := InitMaskCopy.set_range_exists
    oldMask range finish true maskValid endpoint
    (by simp [range, finish, allocRange, Size.ofBytes, endNat]) (by simpa [finish, Size.ofBytes, endNat, maskLength] using bounds)
  obtain ⟨provenance, provenanceOk⟩ := ProvenanceCopy.clear_exists oldProvenance
    range finish raw endpoint
    (by simpa [Allocation.len] using ProvenanceCopy.WellFormed.pointerBounds provenanceValid)
    (by omega)
  have ordered : offset ≤ offset + 1 := UInt64.le_iff_toNat_le.mpr (by omega)
  have bounded : offset + 1 ≤ capacity := UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨sliceBytes, slice, sliceLen⟩ := AllocationCopy.raw_slice_exists
    (return_alloc raw (Size.ofBytes capacity) oldProvenance oldMask align .Mut extra native : Allocation Provenance Extra)
    range finish (by simpa [Allocation.len, Allocation.byteSize, Size.ofBytes] using storage) endpoint ordered bounded
  unfold Allocation.getBytesUnchecked at slice
  have bytesSize : (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
      raw.extract (offset.toNat + 1) raw.size).size = (Size.ofBytes capacity).bytes.toNat := by
    simp only [Array.size_append, Array.size_extract, Array.size_singleton]
    have sz : raw.size = capacity.toNat := storage
    have sz' : (Size.ofBytes capacity).bytes.toNat = capacity.toNat := rfl
    omega
  refine ⟨return_alloc (raw.extract 0 offset.toNat ++ #[if value then 1 else 0] ++
      raw.extract (offset.toNat + 1) raw.size) (Size.ofBytes capacity) provenance mask
      align .Mut extra native, ?_, ?_, rfl, rfl, rfl⟩
  · unfold Allocation.writeScalar
    have pointerSize : Size.fromBits layout.pointerWidth.bits = Size.ofBytes 8 := by rw [width]; rfl
    unfold_internal ".Miri.Memory.pointerSize"
    rw [pointerSize]
    have converted : (Scalar.fromBool value : Scalar Provenance).toBitsOrPtrInternal range.size =
        .ok (.bits (if value then 1 else 0)) := by
      cases value <;> rfl
    simp only [show (Mutability.Mut != Mutability.Mut) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [converted]
    simp only [Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [slice]
    erw [maskOk]
    simp only [Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [provenanceOk]
    rw [show range.size = Size.ofBytes 1 from rfl, bool_encode]
    simp only [range, allocRange, Size.ofBytes]
    simp only [Array.size_append, Array.size_extract, Array.size_singleton] at bytesSize
    simp only [range, allocRange, Size.ofBytes] at bytesSize
    simp [endNat, bytesSize, Array.append_assoc, Id.run]
    omega
  · simpa [Allocation.len] using bytesSize.trans storage.symm

/-- Pure storage mutation for the original general destination window. This needs
no initialized old byte or successful memory-operation premise. -/
theorem from_input {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (layout : TargetDataLayout) (width : layout.pointerWidth.bits = 64) (value : Bool) :
    ∃ updated, Allocation.writeScalar layout
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) (Scalar.fromBool value)
      input.entry.allocation = .ok () updated ∧
      updated.len = input.entry.allocation.len ∧
      updated.byteSize = input.entry.allocation.byteSize ∧
      updated.mutability = .Mut ∧ updated.extra = input.entry.allocation.extra :=
  store input.entry.allocation layout input.capacity input.offset value width input.bytes input.size
    input.mutable input.maskValid input.maskLength input.provenanceMap input.bounds

end DuplicatePrefix.S04ReturnStorage
