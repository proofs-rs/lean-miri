import duplicate_prefix.RootPrimitiveValidation
import duplicate_prefix.RootUsizeWrite

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RootGenericBoolWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem bool_sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
theorem bool_initialized : CopyCompilerFacts.initializedScalar RootCompilerFacts.boolLayout = true := by decide +kernel
theorem bool_type : RootCompilerFacts.boolLayout.ty = 0 := by decide +kernel

theorem validate_nested_bool_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (boolean : Bool)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromBool boolean))))
    (cached : frame.locals[localId].layout = some RootCompilerFacts.boolLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.boolLayout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout bool_initialized
  exact RootPrimitiveValidation.validate_nested_primitive_shallow options remaining span debugOff fuel
    framesBefore frame machine localId RootCompilerFacts.boolLayout (ScalarInt.ofBool boolean) valid live cached
    ghostFalse shallow bool_sized primitive range repr .boolean "bool" (Or.inr ⟨boolean, rfl, rfl⟩)
    (fun base => by simpa only [bool_type] using ScalarValidityQueries.hooks_bool_kind base ())
    (fun base => by simpa only [bool_type] using ScalarValidityQueries.hooks_bool_name base ())

theorem write_bool_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (boolean : Bool)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () (.scalar (Scalar.fromBool boolean))
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromBool boolean))), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate (.scalar (Scalar.fromBool boolean))), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent framesBefore postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining + 1) span debugOff framesBefore frame machine localId
    old (.scalar (Scalar.fromBool boolean)) RootCompilerFacts.boolLayout valid live bool_sized noClocks ghostFalse
  have enforced : hooks.enforceValidity () RootCompilerFacts.boolLayout postState = .ok true postState := by
    change config.projection.place.enforceValidity () RootCompilerFacts.boolLayout postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromBool boolean))) := by
    simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some RootCompilerFacts.boolLayout := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  have validated : hooks.validate ()
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.boolLayout) postState = .ok () postState := by
    change config.projection.place.validate () _ postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel]
    exact validate_nested_bool_shallow options remaining span debugOff fuel framesBefore postFrame machine localId boolean
      postValid postLive postCached ghostFalse shallow
  change writePlaceImmediate hooks () (.scalar (Scalar.fromBool boolean))
    (LocalPlaces.localRuntimePlace framesBefore.size frame localId RootCompilerFacts.boolLayout) _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validated

#print axioms write_bool_shallow
#print axioms validate_nested_bool_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``write_bool_shallow, ``bool_sized, ``bool_initialized, ``bool_type, ``validate_nested_bool_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootGenericBoolWrite
