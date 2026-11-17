import duplicate_prefix.ActualScalarCopy
import duplicate_prefix.RootWriteCallback
import duplicate_prefix.ScalarValidityQueries
import Miri.Input.EvalValidityMachine

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RootUsizeWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem validate_nested_usize_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))))
    (cached : frame.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.usizeLayout) true
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
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.usizeLayout
    CopyCompilerFacts.primitive_layouts_initialized.2.2.2
  have typeEq : RootCompilerFacts.usizeLayout.ty = 5 := by decide +kernel
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () RootCompilerFacts.usizeLayout.ty active = .ok .integer active := by
    rw [typeEq, classifyField]
    have query := congrArg (fun f => f active) (ScalarValidityQueries.hooks_usize_kind base ())
    simpa only [pure, EStateM.pure] using query
  have nameQuery : hooks.typeName () RootCompilerFacts.usizeLayout.ty = pure "usize" := by
    rw [typeEq, nameField]
    exact ScalarValidityQueries.hooks_usize_name base ()
  have validator := ScalarCopyStage.validate_primitive_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId RootCompilerFacts.usizeLayout bits
    valid live cached ActualScalarCopy.usize_sized primitive range repr debug ghostFalse retain "usize" .integer
    nameQuery kindQuery (Or.inl rfl) toOpField readField clearField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

theorem write_local_no_validate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false) :
    writePlaceImmediateNoValidate
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits)).place
      () value (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getter : ValidityMachine.validationInProgress
      (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok false (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
    simp [ValidityMachine.validationInProgress, Storage.withCurrent, ghostFalse,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have callback := RootWriteCallback.actual_local_write_callback options remaining span debugOff
    framesBefore frame machine localId old value layout valid live sized noClocks getter
  have callback' : hooks.writeLocalImmediate () localId layout value (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := callback
  have debug : hooks.debugAssertions = false := by
    change config.projection.place.debugAssertions = false
    rw [fields.projectionDebug, debugOff]
  have frameIndex : hooks.frameIndex (Storage.withCurrent framesBefore frame machine) =
      .ok framesBefore.size (Storage.withCurrent framesBefore frame machine) := by
    change config.projection.place.frameIndex _ = _
    rw [fields.projectionFrameIndex]
    simp [Storage.withCurrent, Stack.frameIndex, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, pure, EStateM.pure, Except.pure]
  have getFrame : hooks.getFrame (Storage.withCurrent framesBefore frame machine) =
      .ok frame (Storage.withCurrent framesBefore frame machine) := by
    change config.projection.place.getFrame _ = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  change writePlaceImmediateNoValidate hooks () value
    (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
    (Storage.withCurrent framesBefore frame machine) = _
  simp only [writePlaceImmediateNoValidate, LocalPlaces.localRuntimePlace, sized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have mutable : asMplaceOrMutableLocal hooks () (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok (.immediateLocal localId layout) (Storage.withCurrent framesBefore frame machine) := by
    unfold asMplaceOrMutableLocal LocalPlaces.localRuntimePlace
    simp_local_place
  simp only [bind, EStateM.bind]
  erw [mutable]
  exact callback'

theorem write_usize_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () (.scalar (Scalar.fromScalarInt bits))
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.usizeLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromScalarInt bits))), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate (.scalar (Scalar.fromScalarInt bits))), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent framesBefore postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have physical := write_local_no_validate options limits (remaining + 1) span debugOff framesBefore frame machine localId
    old (.scalar (Scalar.fromScalarInt bits)) RootCompilerFacts.usizeLayout valid live ActualScalarCopy.usize_sized noClocks ghostFalse
  have enforced : hooks.enforceValidity () RootCompilerFacts.usizeLayout postState = .ok true postState := by
    change config.projection.place.enforceValidity () RootCompilerFacts.usizeLayout postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))) := by
    simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some RootCompilerFacts.usizeLayout := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  have validated : hooks.validate ()
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.usizeLayout) postState = .ok () postState := by
    change config.projection.place.validate () _ postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel]
    exact validate_nested_usize_shallow options remaining span debugOff fuel framesBefore postFrame machine localId bits
      postValid postLive postCached ghostFalse shallow
  change writePlaceImmediate hooks () (.scalar (Scalar.fromScalarInt bits))
    (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.usizeLayout) _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validated

#print axioms write_usize_shallow

#print axioms write_local_no_validate

#print axioms validate_nested_usize_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``write_usize_shallow, ``write_local_no_validate, ``validate_nested_usize_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootUsizeWrite
