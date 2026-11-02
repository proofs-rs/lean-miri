import duplicate_prefix.RootEqUncached
import duplicate_prefix.RootUsizeWrite
import duplicate_prefix.RootWriteCallback
import duplicate_prefix.ScalarCopyStage
import duplicate_prefix.ScalarValidityQueries

/-! The actual outer local write and Shallow validation for the root bool guard. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootBoolWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- Actual source `writePlaceImmediateNoValidate` reaches the canonical local
callback after destination conversion, with the frame update retained. -/
theorem no_validate_write_local
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dest : RuntimePlace Provenance) (value : Immediate Provenance)
    (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (live : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
    (layout : dest.layout = RootCompilerFacts.boolLayout)
    (localRef : dest.ref = .local framesBefore.size 4 none frame.localsIdentity)
    (frameIndex : (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).place.frameIndex
        (Storage.withCurrent framesBefore frame machine) = .ok framesBefore.size
          (Storage.withCurrent framesBefore frame machine))
    (getFrame : (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).place.getFrame
        (Storage.withCurrent framesBefore frame machine) = .ok frame
          (Storage.withCurrent framesBefore frame machine))
    (postFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (postFrameEq : postFrame = {frame with locals := (frame.locals.set 4
      {value := .live (.immediate value), layout := frame.locals[4].layout} valid)})
    (validationFalse : ValidityMachine.validationInProgress
      (Storage.withCurrent framesBefore postFrame machine) = .ok false
        (Storage.withCurrent framesBefore postFrame machine))
    (sized : RootCompilerFacts.boolLayout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) :
    writePlaceImmediateNoValidate
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits)).place
      () value dest (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore postFrame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have callback := RootWriteCallback.actual_local_write_callback options remaining span debugOff
    framesBefore frame machine 4 .uninit value RootCompilerFacts.boolLayout valid live
    sized noClocks (by simpa [postFrameEq] using validationFalse)
  rw [fields.projectionWriteLocal] at callback
  rw [fields.debugAbiNoChecks debugOff] at callback
  have callback' : hooks.writeLocalImmediate () 4 RootCompilerFacts.boolLayout value
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore postFrame machine) := by
    change config.projection.place.writeLocalImmediate () 4 RootCompilerFacts.boolLayout value
      (Storage.withCurrent framesBefore frame machine) = _
    rw [fields.projectionWriteLocal, fields.debugAbiNoChecks debugOff]
    rw [← postFrameEq] at callback
    exact callback
  have debug : hooks.debugAssertions = false := by
    change config.projection.place.debugAssertions = false
    rw [fields.projectionDebug, debugOff]
  have frameIndex' : hooks.frameIndex (Storage.withCurrent framesBefore frame machine) =
      .ok framesBefore.size (Storage.withCurrent framesBefore frame machine) := by
    simpa [hooks, ExecutionMachine.projectionHooks, ExecutionMachine.withValidation, config] using frameIndex
  have getFrame' : hooks.getFrame (Storage.withCurrent framesBefore frame machine) =
      .ok frame (Storage.withCurrent framesBefore frame machine) := by
    simpa [hooks, ExecutionMachine.projectionHooks, ExecutionMachine.withValidation, config] using getFrame
  have mutable : asMplaceOrMutableLocal hooks () dest
      (Storage.withCurrent framesBefore frame machine) =
      .ok (.immediateLocal 4 RootCompilerFacts.boolLayout)
        (Storage.withCurrent framesBefore frame machine) := by
    unfold asMplaceOrMutableLocal
    rw [localRef, layout]
    simp_local_place
  change writePlaceImmediateNoValidate hooks () value dest
    (Storage.withCurrent framesBefore frame machine) = _
  simp_local_place


/-- The actual place enforcement hook returns true for the Shallow profile. -/
theorem enforce_shallow
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (limits : ExecutionMachine.Limits)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (mode : machine.user.payload.validation = .Shallow) :
    ((ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).place.enforceValidity
        () RootCompilerFacts.boolLayout (Storage.withCurrent framesBefore frame machine)) =
      .ok true (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  change config.projection.place.enforceValidity () RootCompilerFacts.boolLayout
    (Storage.withCurrent framesBefore frame machine) = _
  rw [fields.projectionEnforce]
  simp [ValidityMachine.enforceValidity, Storage.withCurrent, mode, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]

/-- Actual nested-config validity accepts a whole-local bool scalar during
Shallow validation. The visitor is the canonical `EvalValidityMachine` source
construction, with its real local read, clear, and ghost callbacks. -/
theorem validate_nested_bool_shallow
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (fuel : Nat)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (boolean : Bool) (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (live4 : (frame.locals[4]'(by omega)).value = .live
      (.immediate (.scalar (Scalar.fromBool boolean))))
    (cached4 : (frame.locals[4]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime
      (PreparedContracts.actualConfig options () remaining span).validity () (fuel + 1)
      (LocalPlaces.localRuntimePlace framesBefore.size frame 4 RootCompilerFacts.boolLayout) true
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore frame machine) := by
  let inner := PreparedContracts.actualConfig options () remaining span
  let innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := innerFields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays inner.projection pointers
  let base := ExecutionValidity.hooks queries inner.access inner.allocation inner.compiler
    inner.projection vtable discriminant inner.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime inner.access inner.allocation
    inner.compiler pointers inner.retag options.limits.retag base
  have hooksEq : inner.validity = hooks := by
    rw [validityField]
    rfl
  obtain ⟨typedCompiler, typedDebug, toOpField, readField, clearField, ghostField,
      classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_primitive_fields_unbound
        PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
        PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access
        inner.allocation inner.compiler pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by
    rw [typedDebug, innerFields.debug, debugOff]
  have retain : inner.access.retainTouched = fun machine _ => machine :=
    innerFields.retainTouched
  obtain ⟨primitive, range, repr⟩ : ∃ primitive range, RootCompilerFacts.boolLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)) := by
    refine ⟨.Int .I8 false, ⟨0, 1⟩, ?_⟩
    unfold RootCompilerFacts.boolLayout
    with_unfolding_all rfl
  let activeMachine := {machine with user := {machine.user with payload :=
    {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have boolType : RootCompilerFacts.boolLayout.ty = 0 := by decide +kernel
  have kindQuery : hooks.classify () RootCompilerFacts.boolLayout.ty active = .ok .boolean active := by
    rw [classifyField]
    rw [boolType]
    have q := congrArg (fun f => f active)
      (ScalarValidityQueries.hooks_bool_kind base ())
    simpa [pure, EStateM.pure] using q
  have nameQuery : hooks.typeName () RootCompilerFacts.boolLayout.ty = pure "bool" := by
    rw [nameField]
    rw [boolType]
    exact ScalarValidityQueries.hooks_bool_name base ()
  have localValidator := ScalarCopyStage.validate_primitive_fields_shallow
    hooks inner.access inner.allocation typedCompiler fuel () framesBefore frame machine
    4 RootCompilerFacts.boolLayout (ScalarInt.ofBool boolean) valid4 live4 cached4 (by decide +kernel)
    primitive range repr debug ghostFalse retain "bool" .boolean nameQuery kindQuery
    (Or.inr ⟨boolean, rfl, rfl⟩)
    toOpField readField clearField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively
      (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact localValidator

/-- The local callback samples the actual ghost flag before shallow validation
starts; frame-only layout/value updates leave it false. -/
theorem validation_getter_false_after_local_write
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (value : Immediate Provenance)
    (ghostFalse : machine.user.payload.ghost = false) :
    ValidityMachine.validationInProgress
      (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set 4
          {value := .live (.immediate value), layout := frame.locals[4].layout} valid)} machine) =
      .ok false (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set 4
          {value := .live (.immediate value), layout := frame.locals[4].layout} valid)} machine) := by
  simp [ValidityMachine.validationInProgress, Storage.withCurrent, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ghostFalse]

#print axioms no_validate_write_local
#print axioms enforce_shallow
#print axioms validation_getter_false_after_local_write
#print axioms validate_nested_bool_shallow

end DuplicatePrefix.RootBoolWrite
