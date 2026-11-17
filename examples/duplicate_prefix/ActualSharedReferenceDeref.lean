import duplicate_prefix.SharedReferenceDeref
namespace DuplicatePrefix.ActualSharedReferenceDeref
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem constructor_maximum
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (po : EvalPlaceConstruction.Options) (pointers : RootPointers) (table : RootRawVTable)
    (projection : (PreparedContracts.actualConfig options () remaining span).projection =
      EvalPlaceConstruction.projection PreparedReflection.actual.compiler po
        (PreparedContracts.actualConfig options () remaining span).access
        (PreparedContracts.actualConfig options () remaining span).allocation
        (PreparedContracts.actualConfig options () remaining span).compiler table) :
    po.maxSizeOfVal = Size.ofBytes 9223372036854775807 := by
  let config := PreparedContracts.actualConfig options () remaining span
  obtain ⟨sourceTable,maximum,maximumQuery,dynamicEq⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).projectionDynamic
  have actualMaximum : CompilerExecutionBounds.maximum PreparedReflection.actual.compiler.runtime.target =
      .ok (Size.ofBytes 9223372036854775807) := by rfl
  have maxEq : maximum = Size.ofBytes 9223372036854775807 := Except.ok.inj (maximumQuery.symm.trans actualMaximum)
  have source : config.projection.dynamic.maxSizeOfVal = po.maxSizeOfVal := by rw [projection];rfl
  have target : config.projection.dynamic.maxSizeOfVal = maximum := by rw [dynamicEq];rfl
  rw [target,maxEq] at source
  exact source.symm

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
      ⟨.immediate (RetagReferencePlace.sliceValue config.access.runtime.base pointer len SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
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
  have poMax := constructor_maximum options remaining span po constructorPointers table projectionEq
  have bounded : len ≤ po.maxSizeOfVal.bytes := by
    rw [poMax]
    change len ≤ (9223372036854775807 : UInt64)
    apply UInt64.le_iff_toNat_le.mpr
    change len.toNat ≤ 9223372036854775807
    omega
  have retain : config.access.retainTouched state.machine none = state.machine := by rw [fields.retainTouched]
  change config.operands.dereference () _ state = _
  rw [derefEq,projectionEq]
  exact SharedReferenceDeref.positive_shared_dereference config.access pointers po table state id tag base offset len entry
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
      ⟨.immediate (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
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
  exact SharedReferenceDeref.integer_zero_shared_dereference config.access po table state address width nonzero
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
      ⟨.immediate (RetagReferencePlace.sliceValue config.access.runtime.base pointer 0 SharedReferenceMetadata.sharedLayout).imm,
        SharedReferenceMetadata.sharedLayout⟩ state =
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
  exact SharedReferenceDeref.zero_shared_dereference config.access po table state pointer width nonzero
    fuel poFuel cmp metadata notConstructed retain

#print axioms actual_integer_zero_dereference
#print axioms actual_zero_dereference

#print axioms actual_positive_dereference
end
end DuplicatePrefix.ActualSharedReferenceDeref
