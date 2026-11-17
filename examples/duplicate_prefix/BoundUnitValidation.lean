import duplicate_prefix.CopyHelperUnit
namespace DuplicatePrefix.BoundUnitValidation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CopyHelperUnit
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem with_retag
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (retag : TypedRetag.Hooks MiriMemoryKind Machine.RootUser) (retagBudget : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some layout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime (TypedMachineBindings.bindValidity
      (PreparedContracts.actualConfig options () remaining span).validity retag retagBudget)
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let inner := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := fields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays inner.projection pointers
  let base := ExecutionValidity.hooks queries inner.access inner.allocation inner.compiler
    inner.projection vtable discriminant inner.retag options.limits.retag
  let original := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime inner.access inner.allocation
    inner.compiler pointers inner.retag options.limits.retag base
  let hooks := TypedMachineBindings.bindValidity original retag retagBudget
  have hooksEq : TypedMachineBindings.bindValidity inner.validity retag retagBudget = hooks := by rw [validityField]; rfl
  obtain ⟨typedCompiler, typedDebug, toOpField, readField, clearField, ghostField,
      classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_primitive_fields_unbound
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access inner.allocation inner.compiler
    pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by rw [typedDebug, fields.debug, debugOff]
  have retain := CanonicalConfigFacts.actual_retain_touched options () remaining span
  have typeEq : layout.ty = 2 := by decide +kernel
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok (.aggregate false false false) active := by
    change original.classify () layout.ty active = _
    rw [typeEq, classifyField]
    have query := congrArg (fun f => f active) (hooks_unit_kind base ())
    simpa only [pure, EStateM.pure] using query
  have nameQuery : hooks.typeName () layout.ty = pure "()" := by
    change original.typeName () layout.ty = _
    rw [typeEq, nameField]
    exact hooks_unit_name base ()
  have inhabited : hooks.opsemInhabited () layout.ty active = .ok true active := by
    rw [typeEq]
    change (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).opsemInhabited () 2 active = _
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [unit_inhabited]
    rfl
  have hookDebug : hooks.debugAssertions = false := by
    change inner.compiler.debugAssertions = false
    rw [fields.debug, debugOff]
  have validator := validate_unit_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout
    valid live cached layout_shape.2.1 layout_shape.2.2.1 layout_shape.2.2.2 debug ghostFalse retain "()"
    nameQuery kindQuery inhabited hookDebug toOpField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime (TypedMachineBindings.bindValidity inner.validity retag retagBudget) () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

theorem compiler_validate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some layout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.withValidation (PreparedContracts.actualConfig options () remaining span) limits).compiler.validate
      () (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  rw [CanonicalConfigFacts.with_validation_validate,
    (CanonicalConfigFacts.actual_fields options () remaining span).validationRecursive,validationFuel]
  exact with_retag options remaining span debugOff fuel
    (PreparedContracts.actualConfig options () remaining span).retag limits.retag
    framesBefore frame machine localId valid live cached ghostFalse shallow

#print axioms with_retag
#print axioms compiler_validate
end DuplicatePrefix.BoundUnitValidation
