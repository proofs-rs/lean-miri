import duplicate_prefix.RootUnitAssignment
import duplicate_prefix.RootUsizeAssignment
import duplicate_prefix.SuccessfulTrace
import duplicate_prefix.LocalDirectness
import duplicate_prefix.SevenSteps
namespace DuplicatePrefix.RootLenPrefixStart
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem shared_storage (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).lifecycle.storage.veryTriviallySized 7 = .ok true := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
  with_unfolding_all rfl

theorem executes_preserving
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value = .live (.immediate .uninit))
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate temp5))
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,0⟩)
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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,7⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[10]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[11]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[12]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[13]? = frame.locals[13]? ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame) ∧ resultFrame.trackCallerArg = frame.trackCallerArg ∧
      (∀ index,13 ≤ index → resultFrame.locals[index]? = frame.locals[index]?) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[2]? = some block := by rw [body];simp [block]
  have init7 := unused 7 (by rw [size];decide) (by decide) (by decide)
  have init8 := unused 8 (by rw [size];decide) (by decide) (by decide)
  have init9 := unused 9 (by rw [size];decide) (by decide) (by decide)
  have init10 := unused 10 (by rw [size];decide) (by decide) (by decide)
  have init11 := unused 11 (by rw [size];decide) (by decide) (by decide)
  have init12 := unused 12 (by rw [size];decide) (by decide) (by decide)
  have v1 : (5 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  let f1 := SourceSteps.deadFrame frame ⟨2,0⟩ 5 v1
  have step1 := SourceSteps.storage_dead_exact config limits () framesBefore frame machine ⟨2,0⟩ block stmt0
    5 temp5 location blockAt (by simp [stmt0]) (by with_unfolding_all rfl) v1 (by decide)
    (by simpa [SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using live5)
  have size1 : f1.locals.size = 25 := by simp [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size]
  have v2 : (3 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1];decide
  let f2 := {(ActualLocalCopy.written f1 3 CopyHelperUnit.layout v2 .uninit) with location := .mir ⟨2,2⟩}
  have step2 := RootUnitAssignment.step options limits remaining span source debugOff fuel validationFuel .initial
    framesBefore f1 machine v2 .uninit
    (by simpa [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using live3) (by simpa [f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using uncached3)
    body identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have size2 : f2.locals.size = 25 := by simp [f2,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size1]
  have v3 : (4 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2];decide
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  let f3 := SourceSteps.deadFrame f2 ⟨2,2⟩ 4 v3
  have step3 := SourceSteps.storage_dead_exact config limits () framesBefore f2 machine ⟨2,2⟩ block stmt2
    4 temp4 rfl blockAt (by simp [stmt2]) (by with_unfolding_all rfl) v3 (by decide)
    (by simpa [f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using live4)
  have size3 : f3.locals.size = 25 := by simp [f3,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size2]
  have v4 : (3 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  let stmt3 := block.statements[3]'(by with_unfolding_all decide +kernel)
  let f4 := SourceSteps.deadFrame f3 ⟨2,3⟩ 3 v4
  have step4 := SourceSteps.storage_dead_exact config limits () framesBefore f3 machine ⟨2,3⟩ block stmt3
    3 .uninit rfl blockAt (by simp [stmt3]) (by with_unfolding_all rfl) v4 (by decide)
    (by simp [f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set])
  have size4 : f4.locals.size = 25 := by simp [f4,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size3]
  have v5 : (7 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4];decide
  let stmt4 := block.statements[4]'(by with_unfolding_all decide +kernel)
  let f5 := SourceSteps.liveFrame f4 ⟨2,4⟩ 7 v5
  have step5 := SourceSteps.storage_live_exact config limits () framesBefore f4 machine ⟨2,4⟩ block stmt4
    7 2 rfl blockAt (by simp [stmt4]) (by with_unfolding_all rfl) v5
    (by change frame.body.locals[7]? = _; rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_type2 options () (remaining+1) span)
    (by simpa [f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using congrArg (fun slot => slot.value) init7) noClocks
  have size5 : f5.locals.size = 25 := by simp [f5,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size4]
  have v6 : (8 : Miri.MIR.LocalId) < f5.locals.size := by rw [size5];decide
  let stmt5 := block.statements[5]'(by with_unfolding_all decide +kernel)
  let f6 := SourceSteps.liveFrame f5 ⟨2,5⟩ 8 v6
  have step6 := SourceSteps.storage_live_exact config limits () framesBefore f5 machine ⟨2,5⟩ block stmt5
    8 0 rfl blockAt (by simp [stmt5]) (by with_unfolding_all rfl) v6
    (by change frame.body.locals[8]? = _; rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_bool options () (remaining+1) span)
    (by simpa [f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using congrArg (fun slot => slot.value) init8) noClocks
  have size6 : f6.locals.size = 25 := by simp [f6,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size5]
  have v7 : (9 : Miri.MIR.LocalId) < f6.locals.size := by rw [size6];decide
  let stmt6 := block.statements[6]'(by with_unfolding_all decide +kernel)
  let f7 := SourceSteps.liveFrame f6 ⟨2,6⟩ 9 v7
  have step7 := SourceSteps.storage_live_exact config limits () framesBefore f6 machine ⟨2,6⟩ block stmt6
    9 5 rfl blockAt (by simp [stmt6]) (by with_unfolding_all rfl) v7
    (by change frame.body.locals[9]? = _; rw [body];with_unfolding_all rfl) (CanonicalConfigFacts.actual_storage_usize options () (remaining+1) span)
    (by simpa [f6,f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootUnitAssignment.localIdOf,RootUnitAssignment.location,RootUsizeAssignment.destId,RootUsizeAssignment.siteLocation,Array.getElem_set] using congrArg (fun slot => slot.value) init9) noClocks
  have size7 : f7.locals.size = 25 := by simp [f7,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size6]
  have history : SuccessfulTrace.Trace config limits (Storage.withCurrent framesBefore frame machine)
      (Storage.withCurrent framesBefore f7 machine) :=
    SevenSteps.trace (config := config) (limits := limits)
      (s0 := Storage.withCurrent framesBefore frame machine)
      (s1 := Storage.withCurrent framesBefore f1 machine)
      (s2 := Storage.withCurrent framesBefore f2 machine)
      (s3 := Storage.withCurrent framesBefore f3 machine)
      (s4 := Storage.withCurrent framesBefore f4 machine)
      (s5 := Storage.withCurrent framesBefore f5 machine)
      (s6 := Storage.withCurrent framesBefore f6 machine)
      (s7 := Storage.withCurrent framesBefore f7 machine)
      step1 step2 step3 step4 step5 step6 step7
  have all1 : CopyHelperCleanup.AllImmediate f1 := LocalDirectness.dead frame ⟨2,0⟩ 5 v1 allImmediate
  have all2 : CopyHelperCleanup.AllImmediate f2 := LocalDirectness.written_at f1 3 CopyHelperUnit.layout .uninit v2 ⟨2,2⟩ all1
  have all3 : CopyHelperCleanup.AllImmediate f3 := LocalDirectness.dead f2 ⟨2,2⟩ 4 v3 all2
  have all4 : CopyHelperCleanup.AllImmediate f4 := LocalDirectness.dead f3 ⟨2,3⟩ 3 v4 all3
  have all5 : CopyHelperCleanup.AllImmediate f5 := LocalDirectness.live f4 ⟨2,4⟩ 7 v5 all4
  have all6 : CopyHelperCleanup.AllImmediate f6 := LocalDirectness.live f5 ⟨2,5⟩ 8 v6 all5
  have all7 : CopyHelperCleanup.AllImmediate f7 := LocalDirectness.live f6 ⟨2,6⟩ 9 v7 all6
  have keepHigh (index : Nat) (high : 13 ≤ index) : f7.locals[index]? = frame.locals[index]? := by
    simp [f7,f6,f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,show (3 : Nat) ≠ index by omega,show (4 : Nat) ≠ index by omega,show (5 : Nat) ≠ index by omega,show (7 : Nat) ≠ index by omega,show (8 : Nat) ≠ index by omega,show (9 : Nat) ≠ index by omega]
  generalize finalEq : f7 = final at history all7
  refine ⟨final,⟨history,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,all7⟩,?_,(by rw [←finalEq];exact keepHigh)⟩
  all_goals rw [← finalEq]
  all_goals simp [f7,f6,f5,f4,f3,f2,f1,SourceSteps.deadFrame,SourceSteps.liveFrame,ActualLocalCopy.written,
    LocalPlaces.cachePlaceLayout,size,Array.getElem?_set,init7,init8,init9,init10,init11,init12]

theorem executes_tracked
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value = .live (.immediate .uninit))
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate temp5))
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,0⟩)
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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,7⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[10]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[11]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[12]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[13]? = frame.locals[13]? ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame) ∧ resultFrame.trackCallerArg = frame.trackCallerArg := by
  obtain ⟨result,props,tracked,kept⟩ := executes_preserving options limits remaining span source debugOff fuel validationFuel framesBefore frame machine count temp4 temp5 size live2 cached2 live3 uncached3 live4 live5 unused body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  exact ⟨result,props,tracked⟩

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (count : UInt64) (temp4 temp5 : Immediate Provenance)
    (size : frame.locals.size = 25)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live3 : (frame.locals[3]'(by omega)).value = .live (.immediate .uninit))
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate temp4))
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate temp5))
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,0⟩)
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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,7⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[10]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[11]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[12]? = some ⟨.dead,none⟩ ∧
      resultFrame.locals[13]? = frame.locals[13]? ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame := by
  obtain ⟨result,props,tracked⟩ := executes_tracked options limits remaining span source debugOff fuel validationFuel framesBefore frame machine count temp4 temp5 size live2 cached2 live3 uncached3 live4 live5 unused body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  exact ⟨result,props⟩

#print axioms executes
end DuplicatePrefix.RootLenPrefixStart
