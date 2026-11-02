import duplicate_prefix.PtrMetadataExecution
/-! Four actual MIR statement steps of the metadata wrapper, starting from uncached return/temp locals and preserving the real machine and return continuation. -/
namespace DuplicatePrefix.PtrMetadataBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open PtrMetadataHelper PtrMetadataExecution
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem normalized_local0 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 5 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem compute_local0
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok RootCompilerFacts.usizeLayout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := normalized_local0 frame sourceBody identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 5 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [RootCompilerFacts.usize_layout_eq]
  rfl

theorem destination0_uncached
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (uncached : (frame.locals[0]'(by omega)).layout = none)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    (ExecutionMachine.rvalueHooks
      (PreparedContracts.actualConfig options () remaining span) limits).evalPlace
      () ⟨0, #[]⟩ true (Storage.withCurrent framesBefore frame machine) =
    .ok (LocalPlaces.localRuntimePlace framesBefore.size
      (LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.usizeLayout valid) 0
      RootCompilerFacts.usizeLayout)
      (Storage.withCurrent framesBefore
        (LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.usizeLayout valid) machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let state := Storage.withCurrent framesBefore frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.usizeLayout valid
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
  have resolve : hooks.resolveLayout () 0 state = .ok RootCompilerFacts.usizeLayout state := by
    change config.projection.place.resolveLayout () 0 state = .ok RootCompilerFacts.usizeLayout state
    rw [fields.projectionResolveLayout, fields.layout]
    exact compute_local0 framesBefore frame machine body identity callee
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
  have sized : RootCompilerFacts.usizeLayout.layout.isSized = true := ActualScalarCopy.usize_sized
  have localPlace := LocalPlaces.localToPlace_uncached hooks () framesBefore frame machine
    0 framesBefore.size RootCompilerFacts.usizeLayout valid uncached sized
    resolve getFrame frameIndex setCached getCached indexCached
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff
    ⟨0, #[]⟩ (LocalPlaces.localRuntimePlace framesBefore.size updatedFrame 0
      RootCompilerFacts.usizeLayout) updated
  have evaluated := LocalPlaces.evalPlace_local_empty_uncached projection () 0 framesBefore
    frame machine framesBefore.size RootCompilerFacts.usizeLayout valid
    (state := state) (updated := updated) localPlace check
  change PlaceDynamic.evalPlace projection () ⟨0, #[]⟩ true state = _
  exact evaluated


def cache0 (frame : CompilerFrameContext.ActualFrame) (valid : (0 : Miri.MIR.LocalId) < frame.locals.size) :=
  LocalPlaces.cachePlaceLayout frame 0 RootCompilerFacts.usizeLayout valid

def metadataWritten (frame : CompilerFrameContext.ActualFrame) (valid : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (len : UInt64) :=
  writeFrame (cache0 frame valid) 0 (.scalar (.fromScalarInt (.ofUInt64 len)))
    (by simpa [cache0,LocalPlaces.cachePlaceLayout] using valid)

theorem metadata_assignment_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (live2 : frame.locals[2].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        pointer len rawLayout).imm))
    (cached2 : frame.locals[2].layout = some rawLayout)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) ⟨0,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (metadataWritten frame valid0 len) machine) := by
  let hooks := ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let updatedFrame := cache0 frame valid0
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore updatedFrame machine
  have valid0' : (0 : Miri.MIR.LocalId) < updatedFrame.locals.size := by
    simpa [updatedFrame,cache0,LocalPlaces.cachePlaceLayout] using valid0
  have valid2' : (2 : Miri.MIR.LocalId) < updatedFrame.locals.size := by
    simpa [updatedFrame,cache0,LocalPlaces.cachePlaceLayout] using valid2
  have live0' : updatedFrame.locals[0].value = .live (.immediate .uninit) := by
    simpa [updatedFrame,cache0,LocalPlaces.cachePlaceLayout] using live0
  have cached0' : updatedFrame.locals[0].layout = some RootCompilerFacts.usizeLayout := by
    simp [updatedFrame,cache0,LocalPlaces.cachePlaceLayout]
  have live2' : updatedFrame.locals[2].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
        pointer len rawLayout).imm) := by
    simpa [updatedFrame,cache0,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live2
  have cached2' : updatedFrame.locals[2].layout = some rawLayout := by
    simpa [updatedFrame,cache0,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached2
  have initialDest := destination0_uncached options limits (remaining+1) span debugOff framesBefore frame machine
    valid0 uncached0 sourceBody identity callee
  have cachedDest := RootOperandCopy.destination_cached_local options limits (remaining+1) span debugOff
    framesBefore updatedFrame machine 0 RootCompilerFacts.usizeLayout valid0' cached0' ActualScalarCopy.usize_sized
  have cacheEffect : evalRvalueIntoPlace hooks () (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) ⟨0,#[]⟩ state0 =
      evalRvalueIntoPlace hooks () (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) ⟨0,#[]⟩ state1 := by
    unfold evalRvalueIntoPlace
    simp only [bind,EStateM.bind]
    rw [initialDest,cachedDest]
    rfl
  rw [cacheEffect]
  exact metadata_assignment_cached options limits remaining span debugOff fuel validationFuel framesBefore updatedFrame machine
    pointer len valid0' valid2' live0' cached0' live2' cached2' noClocks ghostFalse shallow

theorem actual_four_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm))
    (cached1 : (frame.locals[1]'(by omega)).layout = some rawLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ first second third done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (Storage.withCurrent framesBefore first machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore first machine) =
        (Storage.withCurrent framesBefore second machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore second machine) =
        (Storage.withCurrent framesBefore third machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore third machine) =
        (Storage.withCurrent framesBefore done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧ done.extra = frame.extra ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧
      done.locals.size = 3 ∧ done.location = .mir ⟨0,4⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (done.locals[2]?.map (·.value)) = some .dead := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let value := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm
  have valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let block := PtrMetadataHelper.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let stmt1 := block.statements[1]'(by with_unfolding_all decide +kernel)
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let stmt3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  have blockAt : PtrMetadataHelper.body.body.basicBlocks[0]? = some block := by simp [block]
  have stmtAt0 : block.statements[0]? = some stmt0 := by simp [stmt0]
  have stmtAt1 : block.statements[1]? = some stmt1 := by simp [stmt1]
  have stmtAt2 : block.statements[2]? = some stmt2 := by simp [stmt2]
  have stmtAt3 : block.statements[3]? = some stmt3 := by simp [stmt3]
  have kind0 : stmt0.kind = .StorageLive 2 := by with_unfolding_all rfl
  have kind1 : stmt1.kind = .Assign ⟨2,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes) := by with_unfolding_all rfl
  have kind2 : stmt2.kind = .Assign ⟨0,#[]⟩ (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) := by with_unfolding_all rfl
  have kind3 : stmt3.kind = .StorageDead 2 := by with_unfolding_all rfl
  have trivial : config.lifecycle.storage.veryTriviallySized 154 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    decide +kernel
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 2 valid2
  have step1 := SourceSteps.storage_live_exact config limits () framesBefore frame machine ⟨0,0⟩ block stmt0
    2 154 location (by rw [sourceBody];exact blockAt) stmtAt0 kind0 valid2
    (by rw [sourceBody];with_unfolding_all rfl) trivial dead2 noClocks
  have firstSize : first.locals.size = 3 := by simp [first,SourceSteps.liveFrame,size]
  have firstValid0 : (0 : Miri.MIR.LocalId) < first.locals.size := by rw [firstSize];decide
  have firstValid1 : (1 : Miri.MIR.LocalId) < first.locals.size := by rw [firstSize];decide
  have firstValid2 : (2 : Miri.MIR.LocalId) < first.locals.size := by rw [firstSize];decide
  have copyEffect := copy_assignment_uncached options limits remaining span debugOff fuel validationFuel framesBefore first machine pointer len
    firstValid1 firstValid2
    (by simpa [first,SourceSteps.liveFrame,Array.getElem_set,value] using live1)
    (by simpa [first,SourceSteps.liveFrame,Array.getElem_set] using cached1)
    (by simp [first,SourceSteps.liveFrame])
    (by simpa [first,SourceSteps.liveFrame] using uncached2)
    sourceBody identity callee noClocks tracker tracked defaultMode ghostFalse shallow
  let copied := copied2 first firstValid2 value
  let second := {copied with location := .mir ⟨0,2⟩}
  have step2 := SourceSteps.assign_exact config limits () framesBefore first copied machine machine
    ⟨0,1⟩ block stmt1 ⟨2,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes) rfl
    (by change frame.body.basicBlocks[0]? = _;rw [sourceBody];exact blockAt) stmtAt1 kind1 copyEffect rfl
  have secondSize : second.locals.size = 3 := by simp [second,copied,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,firstSize]
  have secondValid0 : (0 : Miri.MIR.LocalId) < second.locals.size := by rw [secondSize];decide
  have secondValid2 : (2 : Miri.MIR.LocalId) < second.locals.size := by rw [secondSize];decide
  have metaEffect := metadata_assignment_uncached options limits remaining span debugOff fuel validationFuel framesBefore second machine pointer len
    secondValid0 secondValid2
    (by simpa [second,copied,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,first,SourceSteps.liveFrame,Array.getElem_set] using live0)
    (by simpa [second,copied,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,first,SourceSteps.liveFrame,Array.getElem_set] using uncached0)
    (by simp [second,copied,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout,value])
    (by simp [second,copied,copied2,cached2,writeFrame,LocalPlaces.cachePlaceLayout])
    sourceBody identity callee noClocks ghostFalse shallow
  let written := metadataWritten second secondValid0 len
  let third := {written with location := .mir ⟨0,3⟩}
  have step3 := SourceSteps.assign_exact config limits () framesBefore second written machine machine
    ⟨0,2⟩ block stmt2 ⟨0,#[]⟩ (.UnaryOp .PtrMetadata (.Move ⟨2,#[]⟩)) rfl
    (by change frame.body.basicBlocks[0]? = _;rw [sourceBody];exact blockAt) stmtAt2 kind2 metaEffect rfl
  have thirdSize : third.locals.size = 3 := by simp [third,written,metadataWritten,cache0,writeFrame,LocalPlaces.cachePlaceLayout,secondSize]
  have thirdValid2 : (2 : Miri.MIR.LocalId) < third.locals.size := by rw [thirdSize];decide
  let done := SourceSteps.deadFrame third ⟨0,3⟩ 2 thirdValid2
  have thirdLive2 : third.locals[2].value = .live (.immediate value) := by
    simp [third,written,metadataWritten,cache0,writeFrame,LocalPlaces.cachePlaceLayout,
      second,copied,copied2,cached2,Array.getElem_set]
  have step4 := SourceSteps.storage_dead_exact config limits () framesBefore third machine ⟨0,3⟩ block stmt3
    2 value rfl (by change frame.body.basicBlocks[0]? = _;rw [sourceBody];exact blockAt) stmtAt3 kind3 thirdValid2 (by decide) thirdLive2
  refine ⟨first,second,third,done,step1,step2,step3,step4,?_⟩
  simp [done,SourceSteps.deadFrame,third,written,metadataWritten,cache0,writeFrame,LocalPlaces.cachePlaceLayout,
    second,copied,copied2,cached2,first,SourceSteps.liveFrame,size,Array.getElem?_set,Array.getElem_set]

#print axioms actual_four_statements

#print axioms metadata_assignment_uncached

open Lean Elab Command in
run_cmd do
  for declaration in #[``actual_four_statements, ``metadata_assignment_uncached] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end
end DuplicatePrefix.PtrMetadataBody
