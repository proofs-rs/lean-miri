import duplicate_prefix.PtrMetadataBody
import duplicate_prefix.PtrMetadataIntegerExecution
namespace DuplicatePrefix.PtrMetadataIntegerBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open PtrMetadataHelper PtrMetadataExecution PtrMetadataBody
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem metadata_assignment_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (address len : UInt64)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (live2 : frame.locals[2].value = .live (.immediate
      (RetagReferencePlace.integerSliceValue address len rawLayout).imm))
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
      (RetagReferencePlace.integerSliceValue address len rawLayout).imm) := by
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
  exact PtrMetadataIntegerExecution.metadata_assignment_cached options limits remaining span debugOff fuel validationFuel framesBefore updatedFrame machine
    address len valid0' valid2' live0' cached0' live2' cached2' noClocks ghostFalse shallow

theorem actual_four_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (address len : UInt64)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (RetagReferencePlace.integerSliceValue address len rawLayout).imm))
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
  let value := (RetagReferencePlace.integerSliceValue address len rawLayout).imm
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
  have copyEffect := PtrMetadataIntegerExecution.copy_assignment_uncached options limits remaining span debugOff fuel validationFuel framesBefore first machine address len
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
  have metaEffect := PtrMetadataIntegerBody.metadata_assignment_uncached options limits remaining span debugOff fuel validationFuel framesBefore second machine address len
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
end
end DuplicatePrefix.PtrMetadataIntegerBody
