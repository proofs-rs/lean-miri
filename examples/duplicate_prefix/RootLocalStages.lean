import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.LocalOperands
import duplicate_prefix.LocalPlaces
import duplicate_prefix.OperandDispatch
import duplicate_prefix.RootConstantStage
import duplicate_prefix.ImmediateReadProof
import duplicate_prefix.RvalueDispatch
import duplicate_prefix.CallEntryFacts
import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerPlaceTypes

/-! Small canonical-machine bridges for the root guard assignment. These
lemmas retain the interpreter's real local operations and only discharge the
place-type debug branch selected by the canonical options. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.RootLocalStages
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev RootConfig := CanonicalConfigFacts.RootConfig

theorem operand_check_skipped
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (place : Place) (op : OpTy Provenance) (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options choice remaining span) limits)).checkPlaceType
      choice place op state = .ok () state := by
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  have debugOff' : (PreparedContracts.actualConfig options choice remaining span).compiler.debugAssertions = false :=
    by rw [fields.debug, debugOff]
  simp [ExecutionMachine.operandHooks, ExecutionMachine.withValidation,
    TypedMachineBindings.bindValidation, debugOff', pure, EStateM.pure]

/-- The canonical machine evaluates a whole-local `Move` through the actual
operand dictionary once the source local read's ghost observation is known.
The cached layout, local liveness, no-clock fact, and ghost getter are the
precise local-read premises consumed by the interpreter's `localToOp`. -/
theorem canonical_move_local
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (immediate : Immediate Provenance) (layout : LocalLayout)
    (valid : (5 : Miri.MIR.LocalId) < frame.locals.size)
    (live : (frame.locals[5]'(by omega)).value = .live (.immediate immediate))
    (cached : (frame.locals[5]'(by omega)).layout = some layout)
    (sized : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none)
    (validating : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).compiler.validationInProgress
        (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine)) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "left") (.Move ⟨5, #[]⟩) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate immediate, layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation
    (PreparedContracts.actualConfig options () remaining span) limits)
  have read := LocalOperands.cached_immediate hooks () framesBefore frame machine 5
    immediate layout none valid live cached sized noClocks false validating
  have check := operand_check_skipped options limits () remaining span debugOff
    (OperandDispatch.wholeLocal 5) ⟨.immediate immediate, layout⟩
    (Storage.withCurrent framesBefore frame machine)
  exact OperandDispatch.evalOperandAt_move_wholeLocal hooks ()
    (OperandPath.rvalue "left") 5 none _ _ _ read check

theorem place_check_skipped
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (choice : Unit) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (place : Place) (value : RuntimePlace Provenance)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    ((ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options choice remaining span) limits)).place.checkPlaceType
      choice place value state) = .ok () state := by
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  change (PreparedContracts.actualConfig options choice remaining span).projection.place.checkPlaceType
    choice place value state = .ok () state
  rw [fields.projectionPlaceType]
  simp [CompilerPlaceTypes.place, CompilerPlaceTypes.check, debugOff,
    pure, EStateM.pure]

/-- Cached whole-local destination evaluation through the actual projection
and place hooks, with the exact stack index derived from the pushed frame. -/
theorem canonical_destination_local
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (layout : LocalLayout) (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (cached : (frame.locals[4]'(by omega)).layout = some layout)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨4, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size frame 4 layout)
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached hooks () frame 4 framesBefore.size
    layout state valid getFrame frameIndex cached sized
  have check := place_check_skipped options limits () remaining span debugOff
    ⟨4, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size frame 4 layout) state
  have evaluated := LocalPlaces.evalPlace_local_empty projection () 4 frame framesBefore.size
    layout state localPlace check
  change PlaceDynamic.evalPlace projection () ⟨4, #[]⟩ true state =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size frame 4 layout) state
  exact evaluated

/-- The rvalue dictionary's immediate read uses the actual access hook; the
canonical root configuration's retain hook is identity for all touched states. -/
theorem canonical_read_scalar
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (scalar : Scalar Provenance) (layout : LocalLayout)
    (readable : ∃ primitive range, layout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range))) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).readImmediate
      () ⟨.immediate (.scalar scalar), layout⟩ state =
    .ok ⟨.scalar scalar, layout⟩ state := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have retain := fields.retainTouched
  have retainNone : config.access.retainTouched state.machine none = state.machine := by
    rw [retain]
  have read := ImmediateReadProof.read_scalar_immediate config.access
    state scalar layout readable retainNone
  simpa [ExecutionMachine.rvalueHooks, ExecutionMachine.withValidation, config] using read

/-- The root's uncached local4 destination goes through the actual compiler
resolver, caches its canonical bool layout in the frame, then passes the actual
place type check with debug assertions disabled. -/
theorem canonical_destination_local_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨4, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid) 4
      RootCompilerFacts.boolLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 4 RootCompilerFacts.boolLayout valid
  let updated := Storage.withCurrent framesBefore updatedFrame machine
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore frame machine
  have frameIndex : hooks.frameIndex state = .ok framesBefore.size state := by
    change config.projection.place.frameIndex state = .ok framesBefore.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have resolve : hooks.resolveLayout () 4 state = .ok RootCompilerFacts.boolLayout state := by
    change config.projection.place.resolveLayout () 4 state = .ok RootCompilerFacts.boolLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact CallEntryFacts.root_compute_local4 framesBefore frame machine body identity callee
  have setCached : hooks.setFrame updatedFrame state = .ok () updated := by
    change config.projection.place.setFrame updatedFrame state = .ok () updated
    rw [fields.projectionSetFrame]
    exact Storage.set_current_frame framesBefore frame updatedFrame machine
  have getCached : hooks.getFrame updated = .ok updatedFrame updated := by
    change config.projection.place.getFrame updated = .ok updatedFrame updated
    rw [fields.projectionGetFrame]
    exact Storage.current_frame framesBefore updatedFrame machine
  have indexCached : hooks.frameIndex updated = .ok framesBefore.size updated := by
    change config.projection.place.frameIndex updated = .ok framesBefore.size updated
    rw [fields.projectionFrameIndex]
    simp [updated, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have sized : RootCompilerFacts.boolLayout.layout.isSized = true := by decide +kernel
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    4 framesBefore.size RootCompilerFacts.boolLayout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := place_check_skipped options limits () remaining span debugOff
    ⟨4, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 4
      RootCompilerFacts.boolLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 4 framesBefore
    frame machine framesBefore.size RootCompilerFacts.boolLayout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨4, #[]⟩ true state = _
  exact evaluated

/-- The root site's actual `OperandMachine.evalOperandAt` selects the exact
compiler constant site and evaluates literal zero through the prepared
constant evidence. -/
theorem canonical_zero_constant_operand
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨0, 4⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    OperandMachine.evalOperandAt
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () remaining span) limits))
      () (OperandPath.rvalue "right")
      (.Constant RootConstantStage.zeroConstant) (some RootCompilerFacts.usizeLayout)
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 0))),
      RootCompilerFacts.usizeLayout⟩ (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨externStatic, constantAt⟩ := fields.constantAt debugOff
  have site : CompilerOperandSites.current
      ((OperandPath.rvalue "right").push (.field "constant"))
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.zeroGuardSite (Storage.withCurrent framesBefore frame machine) := by
    change CompilerOperandSites.current
      ((OperandPath.rvalue "right").push (.field "constant"))
      (Storage.withCurrent framesBefore frame machine) = _
    simp [CompilerOperandSites.current, MachineHooks.currentFrame,
      Storage.withCurrent, Stack.currentFrame?, RootCompilerFacts.zeroGuardSite,
      bodyIndex, location, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, pure, EStateM.pure,
      OperandPath.rvalue]
  have siteLit : CompilerOperandSites.current
      #[.field "kind", .field "rvalue", .field "right", .field "constant"]
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.zeroGuardSite (Storage.withCurrent framesBefore frame machine) := by
    simpa [OperandPath.rvalue] using site
  have result := RootConstantStage.zero_eval_at_bound source config.functions
    config.arithmetic externStatic framesBefore frame machine bodyIndex location fnInstance
  change config.operands.constantAt ()
      ((OperandPath.rvalue "right").push (.field "constant"))
      RootConstantStage.zeroConstant (some RootCompilerFacts.usizeLayout) state = _
  rw [constantAt]
  simpa [siteLit, state, config, RootConstantStage.zeroConstant,
    OperandPath.rvalue, bind, EStateM.bind, pure, EStateM.pure] using result

/-- Every pre-write stage of the root's `n == 0` guard assignment succeeds
through the actual assembled hooks. The conclusion is the real final write
action itself, so this theorem does not assume that write succeeds. -/
theorem canonical_root_eq_to_write
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64) (boolLayout : LocalLayout)
    (valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (cached4 : (frame.locals[4]'(by omega)).layout = some boolLayout)
    (boolSized : boolLayout.layout.isSized = true)
    (valid5 : (5 : Miri.MIR.LocalId) < frame.locals.size)
    (live5 : (frame.locals[5]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (usizeSized : RootCompilerFacts.usizeLayout.layout.backendRepr.isUnsized = false)
    (usizeReadable : ∃ primitive range, RootCompilerFacts.usizeLayout.layout.backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := range)))
    (noClocks : frame.extra.dataRace = none)
    (validationGetter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).compiler.validationInProgress
        (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine))
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨0, 4⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance)
    (classification : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).classify
        () RootCompilerFacts.usizeLayout.ty = pure (.integer .usize))
    (boolQuery : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).boolLayout
        () = pure boolLayout)
    (usizeWidth : RootCompilerFacts.usizeLayout.layout.size = Size.ofBytes 8) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks
        (PreparedContracts.actualConfig options () remaining span) limits) ()
      (.BinaryOp .Eq (.Move ⟨5, #[]⟩) (.Constant RootConstantStage.zeroConstant))
      ⟨4, #[]⟩ (Storage.withCurrent framesBefore frame machine) =
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () (.scalar (.fromBool (n == 0)))
      (LocalPlaces.localRuntimePlace framesBefore.size frame 4 boolLayout)
      (Storage.withCurrent framesBefore frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let hooks := ExecutionMachine.rvalueHooks config limits
  let destValue := LocalPlaces.localRuntimePlace framesBefore.size frame 4 boolLayout
  let nScalar : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 n)
  let zeroScalar : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 0)
  let leftOp : OpTy Provenance := ⟨.immediate (.scalar nScalar), RootCompilerFacts.usizeLayout⟩
  let rightOp : OpTy Provenance := ⟨.immediate (.scalar zeroScalar), RootCompilerFacts.usizeLayout⟩
  let leftImm : RvalueImmTy Provenance := ⟨.scalar nScalar, RootCompilerFacts.usizeLayout⟩
  let rightImm : RvalueImmTy Provenance := ⟨.scalar zeroScalar, RootCompilerFacts.usizeLayout⟩
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromBool (n == 0)), boolLayout⟩
  have dest := canonical_destination_local options limits remaining span debugOff
    framesBefore frame machine boolLayout valid4 cached4 boolSized
  have left := canonical_move_local options limits remaining span debugOff framesBefore
    frame machine (.scalar (.fromScalarInt (.ofUInt64 n))) RootCompilerFacts.usizeLayout
    valid5 live5 cached5 usizeSized noClocks validationGetter
  have leftRead := canonical_read_scalar options limits remaining span state nScalar
    RootCompilerFacts.usizeLayout usizeReadable
  have rightEval := canonical_zero_constant_operand options limits remaining span source debugOff
    framesBefore frame machine bodyIndex location fnInstance
  have rightRead := canonical_read_scalar options limits remaining span state zeroScalar
    RootCompilerFacts.usizeLayout usizeReadable
  have binary := RvalueDispatch.canonical_usize_eq_binary_stage config limits
    RootCompilerFacts.usizeLayout boolLayout n 0 state classification boolQuery usizeWidth
  have destLayout : result.layout = hooks.placeLayout destValue := by
    rfl
  have evalLeft : hooks.evalOperandAt () (OperandPath.rvalue "left") (.Move ⟨5, #[]⟩) none state =
      .ok leftOp state := by
    simpa [hooks, config, leftOp, nScalar, ExecutionMachine.rvalueHooks,
      ExecutionMachine.operandHooks, ExecutionMachine.withValidation] using left
  have evalRight : hooks.evalOperandAt () (OperandPath.rvalue "right")
      (.Constant RootConstantStage.zeroConstant) (some leftImm.layout) state =
      .ok rightOp state := by
    simpa [hooks, config, rightOp, leftImm, ExecutionMachine.rvalueHooks,
      ExecutionMachine.operandHooks, ExecutionMachine.withValidation] using rightEval
  have readLeft : hooks.readImmediate () leftOp state = .ok leftImm state := by
    simpa [hooks, leftOp, leftImm, nScalar] using leftRead
  have readRight : hooks.readImmediate () rightOp state = .ok rightImm state := by
    simpa [hooks, rightOp, rightImm, zeroScalar] using rightRead
  have evalDest : hooks.evalPlace () ⟨4, #[]⟩ true state = .ok destValue state := by
    simpa [hooks, config, destValue, ExecutionMachine.rvalueHooks,
      ExecutionMachine.withValidation] using dest
  have binary' : hooks.binaryOp () .Eq leftImm rightImm state = .ok result state := by
    simpa [hooks, result, leftImm, rightImm, nScalar, zeroScalar,
      ScalarOperations.usizeImmediate, ExecutionMachine.rvalueHooks] using binary
  exact RvalueDispatch.binaryOp_to_write hooks () .Eq (.Move ⟨5, #[]⟩)
    (.Constant RootConstantStage.zeroConstant) ⟨4, #[]⟩ destValue leftOp rightOp
    leftImm rightImm result state state state state state state state evalDest evalLeft
    readLeft evalRight readRight binary' destLayout


#print axioms operand_check_skipped
#print axioms canonical_move_local
#print axioms place_check_skipped
#print axioms canonical_zero_constant_operand
#print axioms canonical_destination_local
#print axioms canonical_destination_local_uncached
#print axioms canonical_read_scalar
#print axioms canonical_root_eq_to_write

end DuplicatePrefix.RootLocalStages
