import duplicate_prefix.PhysicalValidatedBoolWrite
import duplicate_prefix.ActualScalarCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalActualBoolWrite
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite
theorem write_actual (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
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
    (outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ∃ updated, (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () (.scalar (Scalar.fromBool value)) ⟨.memory place.mplace,place.layout⟩ state =
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
      enabled extras rootFree childFree initialTree pointer aligned runtimeSize (fun _ => true)
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
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have write : writePlaceImmediateNoValidate hooks () (.scalar (Scalar.fromBool value))
      ⟨.memory place.mplace,place.layout⟩ state = .ok () after := by
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    have sized : place.layout.layout.isSized = true := by rw [layout]; decide +kernel
    simp only [sized, Bool.true_eq_false, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]
    change config.projection.place.writeMemoryNoValidate () (.scalar (Scalar.fromBool value)) place state = _
    rw [fields.projectionWriteMemory]
    have scopedResult : ValidityMachine.scopedAccess config.access state = .ok context.access state := by
      unfold ValidityMachine.scopedAccess ValidityMachine.validationInProgress
      simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure, ghost]
      rw [outerAccessEq]
      rfl
    have enforce : ValidityMachine.enforceValidity state = .ok true state := by
      simp [ValidityMachine.enforceValidity, shallow, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure]
    dsimp only [config] at scopedResult
    simp only [bind, EStateM.bind, scopedResult, enforce]
    exact writtenOk
  have enforced : hooks.enforceValidity () place.layout after = .ok true after := by
    change config.projection.place.enforceValidity () place.layout after = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, after, CanonicalCopy.replaceAllocation, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have checked : hooks.validate () ⟨.memory place.mplace,place.layout⟩ after = .ok () after := by
    change config.projection.place.validate () _ after = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel, layout]
    exact validation
  refine ⟨updated, ?_, tree, byteSize, len, mask, prov, encoded, mutability⟩
  change writePlaceImmediate hooks () (.scalar (Scalar.fromBool value)) ⟨.memory place.mplace,place.layout⟩ state = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [write]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact checked

#print axioms write_actual
end DuplicatePrefix.PhysicalActualBoolWrite
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PhysicalActualBoolWrite.write_actual) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual physical bool write dependency {dependency}"
