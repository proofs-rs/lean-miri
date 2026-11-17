import duplicate_prefix.RootLenPrefixEnd
namespace DuplicatePrefix.RootLenPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem unused_index (id : Nat) (lo : 10 ≤ id) (hi : id ≤ 12) : id = 10 ∨ id = 11 ∨ id = 12 := by omega

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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))) ,some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[13]? = frame.locals[13]? ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame) ∧ resultFrame.trackCallerArg = frame.trackCallerArg ∧
      (∀ index,13 ≤ index → resultFrame.locals[index]? = frame.locals[index]?) := by
  obtain ⟨middle,⟨first,body7,identity7,callee7,extra7,ret7,cont7,size7,loc7,slot0,slot1,slot2,slot7,slot8,slot9,slot10,slot11,slot12,slot13,va7,locals7,all7⟩,track7,keep7⟩ :=
    RootLenPrefixStart.executes_preserving options limits remaining span source debugOff fuel validationFuel
      framesBefore frame machine count temp4 temp5 size live2 cached2 live3 uncached3 live4 live5 unused
      body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  have v2 : (2 : Miri.MIR.LocalId) < middle.locals.size := by rw [size7];decide
  have init2 : (2 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have same2 : middle.locals[2]'v2 = frame.locals[2]'init2 := by
    simpa only [Array.getElem?_eq_getElem v2,Array.getElem?_eq_getElem init2,Option.some.injEq] using slot2
  have v9 : (9 : Miri.MIR.LocalId) < middle.locals.size := by rw [size7];decide
  have state9 : middle.locals[9]'v9 = ⟨.live (.immediate .uninit),none⟩ := by
    simpa only [Array.getElem?_eq_getElem v9,Option.some.injEq] using slot9
  have nextUnused : ∀ id (valid : id < middle.locals.size), 10 ≤ id → id ≤ 12 → middle.locals[id] = ⟨.dead,none⟩ := by
    intro id valid lo hi
    rcases unused_index id lo hi with rfl | rfl | rfl
    · simpa only [Array.getElem?_eq_getElem valid,Option.some.injEq] using slot10
    · simpa only [Array.getElem?_eq_getElem valid,Option.some.injEq] using slot11
    · simpa only [Array.getElem?_eq_getElem valid,Option.some.injEq] using slot12
  obtain ⟨done,⟨last,doneBody,doneIdentity,doneCallee,doneExtra,doneRet,doneCont,doneSize,doneLoc,kept,done9,done10,done11,done12,doneVa,doneLocals,doneAll⟩,doneTrack,doneKeep⟩ :=
    RootLenPrefixEnd.executes_preserving options limits remaining span debugOff fuel validationFuel
      framesBefore middle machine count size7
      (by rw [same2];exact live2) (by rw [same2];exact cached2)
      (by rw [state9]) (by rw [state9]) nextUnused
      (body7.trans body) (identity7.trans identity) (callee7.trans callee) loc7
      (by rw [extra7];exact noClocks) tracker tracked defaultMode ghostFalse shallow all7
  refine ⟨done,⟨SuccessfulTrace.append first last,doneBody.trans body7,doneIdentity.trans identity7,doneCallee.trans callee7,
    doneExtra.trans extra7,doneRet.trans ret7,doneCont.trans cont7,doneSize,doneLoc,?_,?_,?_,?_,?_,done9,done10,done11,done12,?_,doneVa.trans va7,doneLocals.trans locals7,doneAll⟩,doneTrack.trans track7,(fun index high => (doneKeep index high).trans (keep7 index high))⟩
  · exact (kept 0 (by decide) (by decide) (by decide) (by decide)).trans slot0
  · exact (kept 1 (by decide) (by decide) (by decide) (by decide)).trans slot1
  · exact (kept 2 (by decide) (by decide) (by decide) (by decide)).trans slot2
  · exact (kept 7 (by decide) (by decide) (by decide) (by decide)).trans slot7
  · exact (kept 8 (by decide) (by decide) (by decide) (by decide)).trans slot8
  · exact (kept 13 (by decide) (by decide) (by decide) (by decide)).trans slot13

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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))) ,some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
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
      resultFrame.locals.size = 25 ∧ resultFrame.location = .mir ⟨2,11⟩ ∧
      resultFrame.locals[0]? = frame.locals[0]? ∧ resultFrame.locals[1]? = frame.locals[1]? ∧ resultFrame.locals[2]? = frame.locals[2]? ∧
      resultFrame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))) ,some RootCompilerFacts.usizeLayout⟩ ∧
      resultFrame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      resultFrame.locals[13]? = frame.locals[13]? ∧
      resultFrame.vaList = frame.vaList ∧ resultFrame.localsIdentity = frame.localsIdentity ∧
      CopyHelperCleanup.AllImmediate resultFrame := by
  obtain ⟨result,props,tracked⟩ := executes_tracked options limits remaining span source debugOff fuel validationFuel framesBefore frame machine count temp4 temp5 size live2 cached2 live3 uncached3 live4 live5 unused body identity callee location noClocks tracker tracked defaultMode ghostFalse shallow allImmediate
  exact ⟨result,props⟩

#print axioms executes
end DuplicatePrefix.RootLenPrefix
