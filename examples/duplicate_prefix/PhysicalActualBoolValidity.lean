import duplicate_prefix.PhysicalBoolValidation
import duplicate_prefix.RootBoolWrite
import duplicate_prefix.ReferenceVisitorFields
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalActualBoolValidity
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite
theorem validate_actual (context : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = context.access)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (tag : BorTag) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (value : Bool) (fuel : Nat)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (mask : entry.allocation.initializationMask = InitMask.new entry.allocation.byteSize true)
    (encoding : target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot entry.allocation))
    (pointer : mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (emptyProvenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (canonicalHeap : (state.machine.memory.live.filter fun row => row.1 != id).push (id,entry) = state.machine.memory.live)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity () (fuel + 1)
      ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ true state = .ok () state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := fields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays config.projection pointers
  let visitorBase := ExecutionValidity.hooks queries config.access config.allocation config.compiler
    config.projection vtable discriminant config.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime config.access config.allocation
    config.compiler pointers config.retag options.limits.retag visitorBase
  have hooksEq : config.validity = hooks := validityField
  obtain ⟨inner, innerDebug, toOpField, readField, clearField, ghostField, kindField, nameField⟩ :=
    ScalarCopyStage.typed_visitor_primitive_fields_unbound
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
      PreparedReflection.actual.compiler.lifecycle.calls.runtime visitorBase config.access config.allocation
      config.compiler pointers config.retag options.limits.retag
  let placeHooks := ValidityMachine.placeHooks config.access config.allocation (ValidityMachine.compilerPolicy inner)
  have named : hooks.typeName () RootCompilerFacts.boolLayout.ty = pure "bool" := by
    rw [nameField]
    change (CompilerFactAdapters.validityHooks _ visitorBase).typeName () 0 = _
    exact ScalarValidityQueries.hooks_bool_name visitorBase ()
  have classified : hooks.classify () RootCompilerFacts.boolLayout.ty = pure .boolean := by
    rw [kindField]
    change (CompilerFactAdapters.validityHooks _ visitorBase).classify () 0 = _
    exact ScalarValidityQueries.hooks_bool_kind visitorBase ()
  have metadata := ReferenceVisitorFields.typed_reference_metadata
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime visitorBase config.access config.allocation
    config.compiler pointers config.retag options.limits.retag
  have sizing : hooks.sizeAndAlign () ⟨mplace,RootCompilerFacts.boolLayout⟩ = pure (some (Size.ofBytes 1,Align.ONE)) := by
    rw [metadata.2.2.2.2.2]
    unfold DynamicLayout.sizeAndAlignFromMeta
    have sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
    simp only [sized, ↓reduceIte]
    rfl
  have toOpField' : hooks.toOp = fun c place => placeToOp placeHooks c place := toOpField
  have readField' : hooks.readImmediate = (fun c place expected => do
      let op ← placeToOp placeHooks c place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment context.access) op expected) := by
    rw [← accessEq]
    exact readField
  have clearField' : hooks.clearProvenance = (fun c place =>
      ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment context.access) placeHooks c
        ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place) := by
    rw [← accessEq]
    exact clearField
  have actual := PhysicalBoolValidation.validate_on_context context state mplace id tag base entry value
    hooks placeHooks () fuel "bool" width cached present size mutable storage mask encoding pointer aligned runtimeSize
    emptyProvenance canonicalHeap ghost named classified toOpField' readField' clearField' ghostField sizing finish endpoint
  change ValidityMachine.validateRuntime config.validity () (fuel + 1) _ true state = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  have recursive : ValidityMachine.enforceValidityRecursively state = .ok false state := by
    simp [ValidityMachine.enforceValidityRecursively, shallow, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  simp only [bind, EStateM.bind, recursive]
  exact actual

#print axioms validate_actual
end DuplicatePrefix.PhysicalActualBoolValidity
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PhysicalActualBoolValidity.validate_actual) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual physical bool validation dependency {dependency}"
