import duplicate_prefix.PtrMetadataExecution
namespace DuplicatePrefix.PtrMetadataIntegerExecution
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open PtrMetadataHelper PtrMetadataExecution
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem copy_assignment_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (address len : UInt64)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate
      (RetagReferencePlace.integerSliceValue address len rawLayout).imm))
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
    let value := (RetagReferencePlace.integerSliceValue address len rawLayout).imm
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨1,#[]⟩) .Yes) ⟨2,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (copied2 frame valid2 value) machine) := by
  let value := (RetagReferencePlace.integerSliceValue address len rawLayout).imm
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
  have physical := RootPointerCopy.copy_integer_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine 2 .uninit address len destValid destLive destCached sourceClocks ghostFalse shallow
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
    (address len : UInt64)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size) (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (live2 : frame.locals[2].value = .live (.immediate
      (RetagReferencePlace.integerSliceValue address len rawLayout).imm))
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
  let input := RetagReferencePlace.integerSliceValue address len rawLayout
  let op : OpTy Provenance := ⟨.immediate input.imm,rawLayout⟩
  let result : RvalueImmTy Provenance := ⟨.scalar (.fromScalarInt (.ofUInt64 len)),RootCompilerFacts.usizeLayout⟩
  let dest := LocalPlaces.localRuntimePlace framesBefore.size frame 0 RootCompilerFacts.usizeLayout
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have sourceLive : frame.locals[2].value = .live (.immediate input.imm) := by
    simpa only [input] using live2
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
    exact congrFun (actual_integer_metadata options (remaining+1) span address len (CanonicalConfigFacts.actual_target_width options () (remaining+1) span)) state
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
end DuplicatePrefix.PtrMetadataIntegerExecution
