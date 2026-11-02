import duplicate_prefix.RootLenPrefixStart
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.RootLenPrefixEnd
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem executes_preserving
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live9 : (frame.locals[9]'(by omega)).value = .live (.immediate .uninit))
    (uncached9 : (frame.locals[9]'(by omega)).layout = none)
    (unused : ∀ id (valid : id < frame.locals.size), 10 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,7⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (allImmediate : CopyHelperCleanup.AllImmediate frame) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore resultFrame machine) ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      (∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → resultFrame.locals[id]? = frame.locals[id]?) ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame) ∧ resultFrame.trackCallerArg = frame.trackCallerArg ∧
      (∀ index,13 ≤ index → resultFrame.locals[index]? = frame.locals[index]?) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have v9 : (9 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let f1 := {(ActualLocalCopy.written frame 9 RootCompilerFacts.usizeLayout v9
    (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir ⟨2,8⟩}
  have step1 := RootUsizeAssignment.step options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine count .guardCount (by rw [size];decide) v9
    live2 cached2 live9 uncached9 body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow
  have size1 : f1.locals.size = 25 := by simp [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[2]? = some block := by rw [body];simp [block]
  have init10 := unused 10 (by rw [size];decide) (by decide) (by decide)
  have init11 := unused 11 (by rw [size];decide) (by decide) (by decide)
  have init12 := unused 12 (by rw [size];decide) (by decide) (by decide)
  have v10 : (10 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  let stmt8 := block.statements[8]'(by with_unfolding_all decide +kernel)
  let f2 := SourceSteps.liveFrame f1 ⟨2,8⟩ 10 v10
  have step2 := SourceSteps.storage_live_exact config limits () framesBefore f1 machine ⟨2,8⟩ block stmt8
    10 5 rfl blockAt (by simp [stmt8]) (by with_unfolding_all rfl) v10
    (by change frame.body.locals[10]? = _;rw [body];with_unfolding_all rfl)
    (CanonicalConfigFacts.actual_storage_usize options () (remaining+1) span)
    (by simpa [f1,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg (fun slot => slot.value) init10) noClocks
  have size2 : f2.locals.size = 25 := by simp [f2,SourceSteps.liveFrame,size1]
  have v11 : (11 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2];decide
  let stmt9 := block.statements[9]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.liveFrame f2 ⟨2,9⟩ 11 v11
  have step3 := SourceSteps.storage_live_exact config limits () framesBefore f2 machine ⟨2,9⟩ block stmt9
    11 5 rfl blockAt (by simp [stmt9]) (by with_unfolding_all rfl) v11
    (by change frame.body.locals[11]? = _;rw [body];with_unfolding_all rfl)
    (CanonicalConfigFacts.actual_storage_usize options () (remaining+1) span)
    (by simpa [f2,f1,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg (fun slot => slot.value) init11) noClocks
  have size3 : f3.locals.size = 25 := by simp [f3,SourceSteps.liveFrame,size2]
  have v12 : (12 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  let stmt10 := block.statements[10]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.liveFrame f3 ⟨2,10⟩ 12 v12
  have step4 := SourceSteps.storage_live_exact config limits () framesBefore f3 machine ⟨2,10⟩ block stmt10
    12 7 rfl blockAt (by simp [stmt10]) (by with_unfolding_all rfl) v12
    (by change frame.body.locals[12]? = _;rw [body];with_unfolding_all rfl)
    (RootLenPrefixStart.shared_storage options (remaining+1) span)
    (by simpa [f3,f2,f1,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using congrArg (fun slot => slot.value) init12) noClocks
  have all1 : CopyHelperCleanup.AllImmediate f1 := LocalDirectness.written_at frame 9 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) v9 ⟨2,8⟩ allImmediate
  have all2 : CopyHelperCleanup.AllImmediate f2 := LocalDirectness.live f1 ⟨2,8⟩ 10 v10 all1
  have all3 : CopyHelperCleanup.AllImmediate f3 := LocalDirectness.live f2 ⟨2,9⟩ 11 v11 all2
  have all4 : CopyHelperCleanup.AllImmediate f4 := LocalDirectness.live f3 ⟨2,10⟩ 12 v12 all3
  have keepHigh (index : Nat) (high : 13 ≤ index) : f4.locals[index]? = frame.locals[index]? := by
    simp [f4,f3,f2,f1,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,show (9 : Nat) ≠ index by omega,show (10 : Nat) ≠ index by omega,show (11 : Nat) ≠ index by omega,show (12 : Nat) ≠ index by omega]
  refine ⟨f4,⟨.next step1 (.next step2 (.next step3 (.next step4 (.refl _)))),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,all4⟩,?_,keepHigh⟩
  all_goals simp [f4,f3,f2,f1,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size,
    Array.getElem?_set,init10,init11,init12]
  intro id not9 not10 not11 not12
  simp [Ne.symm not9,Ne.symm not10,Ne.symm not11,Ne.symm not12]

theorem executes_tracked
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live9 : (frame.locals[9]'(by omega)).value = .live (.immediate .uninit))
    (uncached9 : (frame.locals[9]'(by omega)).layout = none)
    (unused : ∀ id (valid : id < frame.locals.size), 10 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,7⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (allImmediate : CopyHelperCleanup.AllImmediate frame) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      (SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore resultFrame machine) ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      (∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → resultFrame.locals[id]? = frame.locals[id]?) ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame) ∧ resultFrame.trackCallerArg = frame.trackCallerArg := by
  obtain ⟨result,props,tracked,kept⟩ := executes_preserving options limits remaining span debugOff fuel validationFuel framesBefore frame machine count size live2 cached2 live9 uncached9 unused body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  exact ⟨result,props,tracked⟩

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live9 : (frame.locals[9]'(by omega)).value = .live (.immediate .uninit))
    (uncached9 : (frame.locals[9]'(by omega)).layout = none)
    (unused : ∀ id (valid : id < frame.locals.size), 10 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,7⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (allImmediate : CopyHelperCleanup.AllImmediate frame) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ resultFrame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
        (Storage.withCurrent framesBefore resultFrame machine) ∧
      resultFrame.body = frame.body ∧ resultFrame.bodyIdentity = frame.bodyIdentity ∧
      resultFrame.functionInstance = frame.functionInstance ∧ resultFrame.extra = frame.extra ∧
      resultFrame.returnPlace = frame.returnPlace ∧ resultFrame.returnContinuation = frame.returnContinuation ∧
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      (∀ id, id ≠ 9 → id ≠ 10 → id ≠ 11 → id ≠ 12 → resultFrame.locals[id]? = frame.locals[id]?) ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame := by
  obtain ⟨result,props,tracked⟩ := executes_tracked options limits remaining span debugOff fuel validationFuel framesBefore frame machine count size live2 cached2 live9 uncached9 unused body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  exact ⟨result,props⟩

#print axioms executes
end DuplicatePrefix.RootLenPrefixEnd
