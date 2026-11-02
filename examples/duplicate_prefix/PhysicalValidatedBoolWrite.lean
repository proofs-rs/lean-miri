import duplicate_prefix.PhysicalActualBoolValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalValidatedBoolWrite
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite
theorem write_and_validate (context : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = context.access)
    (fuel : Nat)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool) (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childFree : tracker.global.protectedTags.contains child = false)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (willValidate : MemoryOperandLayout → Bool)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ∃ updated, (do
      PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
        ⟨.memory place.mplace,place.layout⟩ true) state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  obtain ⟨updated, writtenOk, tree, byteSize, len, mask, prov, encoded, mutability⟩ :=
    PhysicalMachineWrite.bool_parent_slot context state place id root child written base count entry tracker value one layout width
      positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend
      enabled extras rootFree childFree initialTree pointer aligned runtimeSize willValidate
  let after := CanonicalCopy.replaceAllocation state id entry.kind updated
  have afterPresent := CanonicalCopy.replace_lookup state id entry.kind updated
  have newSize : updated.byteSize = Size.ofBytes 1 := byteSize.trans (size.trans (congrArg Size.ofBytes one))
  have newMutable : updated.mutability = .Mut := mutability.trans mutable
  have newStorage : updated.len = updated.byteSize.bytes.toNat := by rw [len,byteSize]; exact storage
  have newMask : updated.initializationMask = InitMask.new updated.byteSize true := by rw [byteSize]; exact mask
  have newEncoding : target_bytes context.access.runtime.base updated.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot updated) := by rw [byteSize]; exact encoded
  have canonicalHeap : (after.machine.memory.live.filter fun row => row.1 != id).push (id,⟨entry.kind,updated⟩) = after.machine.memory.live := by
    simp [after, CanonicalCopy.replaceAllocation, Array.filter_push, Array.filter_filter]
  have validation := PhysicalActualBoolValidity.validate_actual context options remaining span accessEq after place.mplace
    id root base ⟨entry.kind,updated⟩ value fuel width cached afterPresent newSize newMutable newStorage newMask newEncoding
    pointer aligned runtimeSize prov canonicalHeap ghost shallow finish endpoint
  rw [layout]
  refine ⟨updated, ?_, tree, byteSize, len, mask, prov, encoded, mutability⟩
  simp only [bind, EStateM.bind]
  rw [writtenOk]
  exact validation

theorem write_and_validate_between (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (fuel : Nat)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool) (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childFree : tracker.global.protectedTags.contains child = false)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (willValidate : MemoryOperandLayout → Bool)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ∃ updated, (do
      PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
        ⟨.memory place.mplace,place.layout⟩ true) state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  obtain ⟨updated, writtenOk, tree, byteSize, len, mask, prov, encoded, mutability⟩ :=
    PhysicalMachineWrite.bool_parent_slot context state place id root child written base count entry tracker value one layout width
      positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend
      enabled extras rootFree childFree initialTree pointer aligned runtimeSize willValidate
  let after := CanonicalCopy.replaceAllocation state id entry.kind updated
  have afterPresent := CanonicalCopy.replace_lookup state id entry.kind updated
  have newSize : updated.byteSize = Size.ofBytes 1 := byteSize.trans (size.trans (congrArg Size.ofBytes one))
  have newMutable : updated.mutability = .Mut := mutability.trans mutable
  have newStorage : updated.len = updated.byteSize.bytes.toNat := by rw [len,byteSize]; exact storage
  have newMask : updated.initializationMask = InitMask.new updated.byteSize true := by rw [byteSize]; exact mask
  have newEncoding : target_bytes context.access.runtime.base updated.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot updated) := by rw [byteSize]; exact encoded
  have canonicalHeap : (after.machine.memory.live.filter fun row => row.1 != id).push (id,⟨entry.kind,updated⟩) = after.machine.memory.live := by
    simp [after, CanonicalCopy.replaceAllocation, Array.filter_push, Array.filter_filter]
  have validation := PhysicalActualBoolValidity.validate_actual validationContext options remaining span accessEq after place.mplace
    id root base ⟨entry.kind,updated⟩ value fuel validationWidth cached afterPresent newSize newMutable newStorage newMask (by rw [sameRuntime]; exact newEncoding)
    pointer aligned validationRuntimeSize prov canonicalHeap ghost shallow finish endpoint
  rw [layout]
  refine ⟨updated, ?_, tree, byteSize, len, mask, prov, encoded, mutability⟩
  simp only [bind, EStateM.bind]
  rw [writtenOk]
  exact validation

#print axioms write_and_validate
end DuplicatePrefix.PhysicalValidatedBoolWrite
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalValidatedBoolWrite.write_and_validate,
      ``DuplicatePrefix.PhysicalValidatedBoolWrite.write_and_validate_between] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved physical validated bool write dependency {dependency}"
