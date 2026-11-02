import duplicate_prefix.RawPointerValidity
import duplicate_prefix.RootPrimitiveValidation

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RootRawPointerValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootPrimitiveValidation

theorem validate_nested_thin_raw_pointer_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (value : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (value))))
    (cached : frame.locals[localId].layout = some layout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (sized : layout.layout.isSized = true)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (pointee : TyId) (name : String)
    (classification : ∀ base : BaseHooks,
      (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
        () layout.ty = pure (.rawPointer pointee true))
    (naming : ∀ base : BaseHooks,
      (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
        () layout.ty = pure name) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let inner := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := fields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays inner.projection pointers
  let base := ExecutionValidity.hooks queries inner.access inner.allocation inner.compiler
    inner.projection vtable discriminant inner.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime inner.access inner.allocation
    inner.compiler pointers inner.retag options.limits.retag base
  have hooksEq : inner.validity = hooks := by rw [validityField]; rfl
  obtain ⟨typedCompiler, typedDebug, toOpField, readField, clearField, ghostField,
      classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_primitive_fields_unbound
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access inner.allocation inner.compiler
    pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by rw [typedDebug, fields.debug, debugOff]
  have retain := CanonicalConfigFacts.actual_retain_touched options () remaining span
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok (.rawPointer pointee true) active := by
    rw [classifyField]
    have query := congrArg (fun f => f active) (classification base)
    simpa only [pure, EStateM.pure] using query
  have nameQuery : hooks.typeName () layout.ty = pure name := by
    rw [nameField]
    exact naming base
  have validator := RawPointerValidity.validate_thin_raw_pointer_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout value
    valid live cached sized primitive range repr debug ghostFalse retain name pointee
    nameQuery kindQuery toOpField readField clearField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

theorem mut_pointer_sized : CopyCompilerFacts.destPointerLayout.layout.isSized = true := by decide +kernel

theorem validate_nested_mut_pointer_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar value)))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.destPointerLayout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.destPointerLayout
    CopyCompilerFacts.primitive_layouts_initialized.2.2.1
  have typeEq : CopyCompilerFacts.destPointerLayout.ty = 8 := by decide +kernel
  exact validate_nested_thin_raw_pointer_shallow options remaining span debugOff fuel framesBefore frame machine
    localId CopyCompilerFacts.destPointerLayout value valid live cached ghostFalse shallow mut_pointer_sized primitive range repr
    1 "*mut u8"
    (fun base => by simpa only [typeEq] using ScalarValidityQueries.hooks_mut_pointer_kind base ())
    (fun base => by simpa only [typeEq] using ScalarValidityQueries.hooks_mut_pointer_name base ())

theorem const_pointer_sized : CopyCompilerFacts.sourcePointerLayout.layout.isSized = true := by decide +kernel

theorem validate_nested_const_pointer_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar value)))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.sourcePointerLayout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.sourcePointerLayout
    CopyCompilerFacts.primitive_layouts_initialized.2.1
  have typeEq : CopyCompilerFacts.sourcePointerLayout.ty = 9 := by decide +kernel
  exact validate_nested_thin_raw_pointer_shallow options remaining span debugOff fuel framesBefore frame machine
    localId CopyCompilerFacts.sourcePointerLayout value valid live cached ghostFalse shallow const_pointer_sized primitive range repr
    1 "*const u8"
    (fun base => by simpa only [typeEq] using ScalarValidityQueries.hooks_const_pointer_kind base ())
    (fun base => by simpa only [typeEq] using ScalarValidityQueries.hooks_const_pointer_name base ())

#print axioms validate_nested_thin_raw_pointer_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``validate_nested_thin_raw_pointer_shallow, ``mut_pointer_sized, ``const_pointer_sized,
      ``validate_nested_mut_pointer_shallow, ``validate_nested_const_pointer_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootRawPointerValidity
