import duplicate_prefix.PhysicalActualBoolWrite
import duplicate_prefix.PrimitiveCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalBoolReturn
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite
theorem copy_return (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
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
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ∃ updated, (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromBool value)),RootCompilerFacts.boolLayout⟩ view state =
      ({state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}},.ok ()) ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  obtain ⟨updated, write, tree, bytes, len, mask, prov, encoding, mutability⟩ :=
    PhysicalActualBoolWrite.write_actual context validationContext options remaining span accessEq validationWidth validationRuntimeSize
      sameRuntime limits fuel validationFuel state place id root child written base count entry tracker value one layout width
      positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend
      enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow finish endpoint
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let bound := ExecutionMachine.withValidation config limits
  let placeHooks := (ExecutionMachine.projectionHooks bound).place
  let dest : RuntimePlace Provenance := ⟨.memory place.mplace,place.layout⟩
  let scalar : Immediate Provenance := .scalar (Scalar.fromBool value)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have destLayout : dest.layout = RootCompilerFacts.boolLayout := layout
  have flag := GenericCallReturn.same_layout_transmute_flag placeHooks bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.boolLayout scalar dest destLayout compatible
  have exactCopy : copyRuntimePlace placeHooks bound.copy () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ dest := by
    rw [flag]; rfl
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout
    RootGenericBoolWrite.bool_initialized
  have copy := ActualScalarCopy.actual_copy_scalar options limits (remaining+1) span debugOff
    RootCompilerFacts.boolLayout scalar dest destLayout _ repr RootGenericBoolWrite.bool_sized
  refine ⟨updated, ?_, tree, bytes, len, mask, prov, encoding, mutability⟩
  change MachineHooks.run (copyRuntimePlace placeHooks bound.copy ()
    ⟨.immediate scalar,RootCompilerFacts.boolLayout⟩ view.toRuntimePlace true) state = _
  rw [destination, exactCopy, copy]
  unfold MachineHooks.run Call.run
  rw [write]

#print axioms copy_return
end DuplicatePrefix.PhysicalBoolReturn
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PhysicalBoolReturn.copy_return) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual physical bool return dependency {dependency}"
