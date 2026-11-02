import duplicate_prefix.RootReferenceDeref
import duplicate_prefix.ActualSharedReferenceDeref
namespace DuplicatePrefix.ActualRootReferenceDeref
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_positive_dereference
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    let pointer := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    config.operands.dereference ()
      ⟨.immediate (RetagReferencePlace.sliceValue config.access.runtime.base pointer len ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩ state =
      .ok (RetagReferencePlace.slicePlace pointer len ProjectionMetadataFacts.sliceLayout) state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,constructorPointers,table,compilerEq,projectionEq,derefEq⟩ := fields.placeConstruction
  obtain ⟨pointers,arithmetic,wiring⟩ := fields.pointerSource
  have width := CanonicalConfigFacts.actual_target_width options () remaining span
  have arithmetic8 : pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    arithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have poFuel : po.dynamicFuel = fuel+1 := by
    have source : config.projection.dynamicFuel = po.dynamicFuel := by rw [projectionEq];rfl
    exact source.symm.trans (fields.projectionDynamicFuel.trans fuelEq)
  have poMax := ActualSharedReferenceDeref.constructor_maximum options remaining span po constructorPointers table projectionEq
  have bounded : len ≤ po.maxSizeOfVal.bytes := by
    rw [poMax]
    change len ≤ (9223372036854775807 : UInt64)
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have retain : config.access.retainTouched state.machine none = state.machine := by rw [fields.retainTouched]
  change config.operands.dereference () _ state = _
  rw [derefEq,projectionEq]
  exact RootReferenceDeref.positive_mutable_dereference config.access pointers po table state id tag base offset len entry
    wiring arithmetic8 width cached present positive nonzero signedFits bounds fuel poFuel cmp metadata notConstructed bounded retain

theorem actual_integer_zero_dereference
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (address : UInt64) (nonzero : address ≠ 0)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.operands.dereference ()
      ⟨.immediate (RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩ state =
      .ok (RetagReferencePlace.integerSlicePlace address 0 ProjectionMetadataFacts.sliceLayout) state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,constructorPointers,table,compilerEq,projectionEq,derefEq⟩ := fields.placeConstruction
  have width := CanonicalConfigFacts.actual_target_width options () remaining span
  have poFuel : po.dynamicFuel = fuel+1 := by
    have source : config.projection.dynamicFuel = po.dynamicFuel := by rw [projectionEq];rfl
    exact source.symm.trans (fields.projectionDynamicFuel.trans fuelEq)
  have retain : config.access.retainTouched state.machine none = state.machine := by rw [fields.retainTouched]
  change config.operands.dereference () _ state = _
  rw [derefEq,projectionEq]
  exact RootReferenceDeref.integer_zero_mutable_dereference config.access po table state address width nonzero
    fuel poFuel cmp metadata notConstructed retain

theorem actual_zero_dereference
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : RootState) (pointer : Pointer Provenance) (nonzero : pointer.offset.bytes ≠ 0)
    (fuel : Nat) (fuelEq : options.place.dynamicFuel = fuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get state).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get state).entries.any (·.value.ty == 4) = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.operands.dereference ()
      ⟨.immediate (RetagReferencePlace.sliceValue config.access.runtime.base pointer 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩ state =
      .ok (RetagReferencePlace.slicePlace pointer 0 ProjectionMetadataFacts.sliceLayout) state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,constructorPointers,table,compilerEq,projectionEq,derefEq⟩ := fields.placeConstruction
  have width := CanonicalConfigFacts.actual_target_width options () remaining span
  have poFuel : po.dynamicFuel = fuel+1 := by
    have source : config.projection.dynamicFuel = po.dynamicFuel := by rw [projectionEq];rfl
    exact source.symm.trans (fields.projectionDynamicFuel.trans fuelEq)
  have retain : config.access.retainTouched state.machine none = state.machine := by rw [fields.retainTouched]
  change config.operands.dereference () _ state = _
  rw [derefEq,projectionEq]
  exact RootReferenceDeref.zero_mutable_dereference config.access po table state pointer width nonzero
    fuel poFuel cmp metadata notConstructed retain

#print axioms actual_integer_zero_dereference
#print axioms actual_zero_dereference

#print axioms actual_positive_dereference
end
end DuplicatePrefix.ActualRootReferenceDeref

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ActualRootReferenceDeref.actual_positive_dereference, ``DuplicatePrefix.ActualRootReferenceDeref.actual_zero_dereference, ``DuplicatePrefix.ActualRootReferenceDeref.actual_integer_zero_dereference] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
