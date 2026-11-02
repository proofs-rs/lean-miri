import duplicate_prefix.PtrMetadataHelper
import duplicate_prefix.RootOperandCopy
import duplicate_prefix.RootPointerCopy
import duplicate_prefix.RootUsizeWrite
import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.SourceSteps
/-! Actual source metadata-wrapper statement effects, including uncached local layout normalization and real raw-pointer/usize writes. -/
namespace DuplicatePrefix.PtrMetadataExecution
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open PtrMetadataHelper
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def writeFrame (frame : CompilerFrameContext.ActualFrame) (id : Miri.MIR.LocalId)
    (value : Immediate Provenance) (valid : id < frame.locals.size) :=
  {frame with locals := (frame.locals.set id
    {value := .live (.immediate value),layout := frame.locals[id].layout} valid)}

theorem normalized_local2 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 2 = .ok 154 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem compute_local2
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok rawLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := normalized_local2 frame sourceBody identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 154 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [raw_layout_eq]
  rfl

theorem destination2_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached : (frame.locals[2]'(by omega)).layout = none)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨2, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame 2 rawLayout valid) 2
      rawLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 2 rawLayout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 2 rawLayout valid
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
  have resolve : hooks.resolveLayout () 2 state = .ok rawLayout state := by
    change config.projection.place.resolveLayout () 2 state = .ok rawLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact compute_local2 framesBefore frame machine body identity callee
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
  have sized : rawLayout.layout.isSized = true := RootPointerCopy.raw_sized
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    2 framesBefore.size rawLayout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨2, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 2
      rawLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 2 framesBefore
    frame machine framesBefore.size rawLayout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨2, #[]⟩ true state = _
  exact evaluated

def cached2 (frame : CompilerFrameContext.ActualFrame) (valid : (2 : Miri.MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 2 rawLayout valid

def copied2 (frame : CompilerFrameContext.ActualFrame) (valid : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (value : Immediate Provenance) :=
  writeFrame (cached2 frame valid) 2 value (by simpa [cached2,LocalPlaces.cachePlaceLayout] using valid)

theorem copy_assignment_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm))
    (cached1 : frame.locals[1].layout = some rawLayout)
    (live2 : frame.locals[2].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[2].layout = none)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let value := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨1,#[]⟩) .Yes) ⟨2,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (copied2 frame valid2 value) machine) := by
  let value := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := cached2 frame valid2
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let stateAfter := Storage.withCurrent framesBefore (copied2 frame valid2 value) machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame 2 rawLayout
  let op : OpTy Provenance := ⟨.immediate value,rawLayout⟩
  have destEval := destination2_uncached options limits (remaining+1) span debugOff framesBefore frame machine
    valid2 uncached2 sourceBody identity callee
  have sourceValid : (1 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using valid1
  have sourceLive : cachedFrame.locals[1].value = .live (.immediate value) := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout,value,Array.getElem_set,show (2 : Nat) ≠ 1 by decide] using live1
  have sourceCached : cachedFrame.locals[1].layout = some rawLayout := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout,Array.getElem_set,show (2 : Nat) ≠ 1 by decide] using cached1
  have sourceClocks : cachedFrame.extra.dataRace = none := noClocks
  have operand := RootOperandCopy.copy_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    1 value rawLayout (OperandPath.rvalue "operand") (some rawLayout) sourceValid sourceLive sourceCached
    (by with_unfolding_all rfl) sourceClocks ghostFalse
  have destValid : (2 : Miri.MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using valid2
  have destLive : cachedFrame.locals[2].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,cached2,LocalPlaces.cachePlaceLayout] using live2
  have destCached : cachedFrame.locals[2].layout = some rawLayout := by
    simp [cachedFrame,cached2,LocalPlaces.cachePlaceLayout]
  have physical := RootPointerCopy.copy_raw_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine 2 .uninit pointer len destValid destLive destCached sourceClocks ghostFalse shallow
  have copied : hooks.copyOp () op dest state1 = .ok () stateAfter := by
    simpa only [hooks,config,op,dest,state1,stateAfter,copied2,cachedFrame,value,writeFrame] using physical
  have scopedCopy : hooks.withRetagMode () .Default (hooks.copyOp () op dest) state1 = .ok () stateAfter := by
    change MachineHooks.withRetagMode .Default (hooks.copyOp () op dest) state1 = .ok () stateAfter
    exact ScalarCopyStage.with_retag_mode_existing .Default (hooks.copyOp () op dest) state1 stateAfter tracker ()
      tracked defaultMode tracked copied
  exact RvalueDispatch.use_operand hooks () (.Copy ⟨1,#[]⟩) .Yes ⟨2,#[]⟩ dest op state0 state1 state1 stateAfter
    destEval operand scopedCopy

theorem metadata_assignment_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size) (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (live2 : frame.locals[2].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        pointer len rawLayout).imm))
    (cached2 : frame.locals[2].layout = some rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) ⟨0,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        (writeFrame frame 0 (.scalar (.fromScalarInt (.ofUInt64 len))) valid0) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let state := Storage.withCurrent framesBefore frame machine
  let input := RetagReferencePlace.sliceValue config.access.runtime.base pointer len rawLayout
  let op : OpTy Provenance := ⟨.immediate input.imm,rawLayout⟩
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromScalarInt (.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩
  let dest := LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.usizeLayout
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have sameTarget : config.access.runtime.base = (PreparedContracts.actualConfig options () remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have sourceLive : frame.locals[2].value = .live (.immediate input.imm) := by
    simpa only [input,sameTarget] using live2
  have copy := RootOperandCopy.copy_cached_local options limits (remaining+1) span debugOff framesBefore frame machine
    2 input.imm rawLayout (OperandPath.rvalue "operand") none valid2 sourceLive cached2
    (by with_unfolding_all rfl) noClocks ghostFalse
  have operand : hooks.evalOperandAt () (OperandPath.rvalue "operand") (.Move ⟨2,#[]⟩) none state = .ok op state := by
    exact copy
  have read : hooks.readImmediate () op state = .ok input state := by
    change PlaceMachine.readImmediate config.access op state = _
    apply read_pair_immediate config.access state _ _ rawLayout raw_readable
    rw [fields.retainTouched]
  have scalar : hooks.unaryOp () .PtrMetadata input state = .ok result state := by
    change ScalarOps.unary (ExecutionMachine.scalarHooks config) () .PtrMetadata input state = _
    exact congrFun (actual_scalar_metadata options (remaining+1) span pointer len) state
  have destEval := RootOperandCopy.destination_cached_local options limits (remaining+1) span debugOff
    framesBefore frame machine 0 RootCompilerFacts.usizeLayout valid0 cached0 ActualScalarCopy.usize_sized
  have staged := CopyLanguageGuard.unary_to_write hooks () .PtrMetadata (.Move ⟨2,#[]⟩) ⟨0,#[]⟩
    dest op input result state destEval operand read scalar rfl
  rw [staged]
  exact RootUsizeWrite.write_usize_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 0 .uninit (.ofUInt64 len) valid0 live0 cached0 noClocks ghostFalse shallow

#print axioms copy_assignment_uncached
#print axioms metadata_assignment_cached
end
end DuplicatePrefix.PtrMetadataExecution
