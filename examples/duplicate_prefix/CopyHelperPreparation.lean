import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.CopyHelperCleanup
namespace DuplicatePrefix.CopyHelperPreparation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_eight_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (source dest : Scalar Provenance) (n : UInt64)
    (size : frame.locals.size = 17)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,0⟩)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar source)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.sourcePointerLayout)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar dest)))
    (cached2 : (frame.locals[2]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (live3 : (frame.locals[3]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached3 : (frame.locals[3]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate (.uninit)))
    (cached4 : (frame.locals[4]'(by omega)).layout = some CopyHelperUnit.layout)
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate (.scalar (.fromBool false))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (uncached14 : (frame.locals[14]'(by omega)).layout = none)
    (dead15 : (frame.locals[15]'(by omega)).value = .dead)
    (uncached15 : (frame.locals[15]'(by omega)).layout = none)
    (dead16 : (frame.locals[16]'(by omega)).value = .dead)
    (uncached16 : (frame.locals[16]'(by omega)).layout = none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ f1 f2 f3 f4 f5 f6 f7 f8 : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f1 machine) =
        (Storage.withCurrent frames f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f2 machine) =
        (Storage.withCurrent frames f3 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f3 machine) =
        (Storage.withCurrent frames f4 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f4 machine) =
        (Storage.withCurrent frames f5 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f5 machine) =
        (Storage.withCurrent frames f6 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f6 machine) =
        (Storage.withCurrent frames f7 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent frames f7 machine) =
        (Storage.withCurrent frames f8 machine,.ok true) ∧
      f8.body = frame.body ∧ f8.bodyIdentity = frame.bodyIdentity ∧ f8.functionInstance = frame.functionInstance ∧
      f8.extra = frame.extra ∧ f8.returnPlace = frame.returnPlace ∧ f8.returnContinuation = frame.returnContinuation ∧
      f8.vaList = frame.vaList ∧ f8.localsIdentity = frame.localsIdentity ∧ f8.locals.size = 17 ∧
      f8.location = .mir ⟨7,8⟩ ∧ f8.locals[0]? = frame.locals[0]? ∧
      CopyHelperCleanup.AllImmediate f8 ∧
      f8.locals[14]? = some ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩ ∧
      f8.locals[15]? = some ⟨.live (.immediate (.scalar dest)),some CopyCompilerFacts.destPointerLayout⟩ ∧
      f8.locals[16]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have v4 : (4 : MIR.LocalId) < frame.locals.size  := by rw [size];decide
  have v5 : (5 : MIR.LocalId) < frame.locals.size  := by rw [size];decide
  have v14 : (14 : MIR.LocalId) < frame.locals.size  := by rw [size];decide
  have v15 : (15 : MIR.LocalId) < frame.locals.size  := by rw [size];decide
  have v16 : (16 : MIR.LocalId) < frame.locals.size  := by rw [size];decide
  have v1stage : (5 : MIR.LocalId) < frame.locals.size := by simpa [SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v5
  let f1 := SourceSteps.deadFrame frame ⟨7,0⟩ 5 v1stage
  have eqf1 : f1 = SourceSteps.deadFrame frame ⟨7,0⟩ 5 v1stage := rfl
  clear_value f1
  have step1 : ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames f1 machine,.ok true) := by
    rw [eqf1]
    exact CopyHelperSteps.storage_dead options limits (remaining+1) span frames frame machine ⟨7,0⟩ 5 (.scalar (.fromBool false))
      sourceBody (by simp [SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location]) (by decide +kernel) (by decide) v1stage
      (by simpa [SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using live5)
  have v2stage : (4 : MIR.LocalId) < f1.locals.size := by simpa [eqf1, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v4
  let f2 := SourceSteps.deadFrame f1 ⟨7,1⟩ 4 v2stage
  have eqf2 : f2 = SourceSteps.deadFrame f1 ⟨7,1⟩ 4 v2stage := rfl
  clear_value f2
  have step2 : ExecutionMachine.step config limits () (Storage.withCurrent frames f1 machine) =
      (Storage.withCurrent frames f2 machine,.ok true) := by
    rw [eqf2]
    exact CopyHelperSteps.storage_dead options limits (remaining+1) span frames f1 machine ⟨7,1⟩ 4 (.uninit)
      (by simpa [eqf1,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simp [eqf1, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location]) (by decide +kernel) (by decide) v2stage
      (by simpa [eqf1, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using live4)
  have v3stage : (14 : MIR.LocalId) < f2.locals.size := by simpa [eqf1, eqf2, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v14
  let f3 := SourceSteps.liveFrame f2 ⟨7,2⟩ 14 v3stage
  have eqf3 : f3 = SourceSteps.liveFrame f2 ⟨7,2⟩ 14 v3stage := rfl
  clear_value f3
  have step3 : ExecutionMachine.step config limits () (Storage.withCurrent frames f2 machine) =
      (Storage.withCurrent frames f3 machine,.ok true) := by
    rw [eqf3]
    exact CopyHelperSteps.storage_live options limits (remaining+1) span frames f2 machine ⟨7,2⟩ 14 9
      (by simpa [eqf1, eqf2,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simp [eqf1, eqf2, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location]) (by decide +kernel) (by decide +kernel) (by decide +kernel) v3stage
      (by simpa [eqf1, eqf2, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using dead14) (by simpa [eqf1, eqf2,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks)
  have v4stage : (14 : MIR.LocalId) < f3.locals.size := by simpa [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v14
  let f4 := CopyHelperSteps.advance (ActualLocalCopy.written f3 14 CopyCompilerFacts.sourcePointerLayout v4stage (.scalar source)) ⟨7,3⟩
  have eqf4 : f4 = CopyHelperSteps.advance (ActualLocalCopy.written f3 14 CopyCompilerFacts.sourcePointerLayout v4stage (.scalar source)) ⟨7,3⟩ := rfl
  clear_value f4
  have step4 : ExecutionMachine.step config limits () (Storage.withCurrent frames f3 machine) =
      (Storage.withCurrent frames f4 machine,.ok true) := by
    rw [eqf4]
    exact CopyHelperSteps.source_copy_step options limits remaining span debugOff fuel validationFuel
      frames f3 machine source (by simpa [eqf1, eqf2, eqf3,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simpa [eqf1, eqf2, eqf3,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using identity) (by simpa [eqf1, eqf2, eqf3,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using callee)
      (by simpa [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using (show (1 : MIR.LocalId) < frame.locals.size by rw [size];decide)) v4stage
      (by simpa [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using live1) (by simpa [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using cached1)
      (by simp [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set]) (by simpa [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using uncached14)
      (by simpa [eqf1, eqf2, eqf3,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks) tracker tracked defaultMode ghost shallow (by simp [eqf1, eqf2, eqf3, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location])
  have v5stage : (15 : MIR.LocalId) < f4.locals.size := by simpa [eqf1, eqf2, eqf3, eqf4, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v15
  let f5 := SourceSteps.liveFrame f4 ⟨7,4⟩ 15 v5stage
  have eqf5 : f5 = SourceSteps.liveFrame f4 ⟨7,4⟩ 15 v5stage := rfl
  clear_value f5
  have step5 : ExecutionMachine.step config limits () (Storage.withCurrent frames f4 machine) =
      (Storage.withCurrent frames f5 machine,.ok true) := by
    rw [eqf5]
    exact CopyHelperSteps.storage_live options limits (remaining+1) span frames f4 machine ⟨7,4⟩ 15 8
      (by simpa [eqf1, eqf2, eqf3, eqf4,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simp [eqf1, eqf2, eqf3, eqf4, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location]) (by decide +kernel) (by decide +kernel) (by decide +kernel) v5stage
      (by simpa [eqf1, eqf2, eqf3, eqf4, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using dead15) (by simpa [eqf1, eqf2, eqf3, eqf4,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks)
  have v6stage : (15 : MIR.LocalId) < f5.locals.size := by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v15
  let f6 := CopyHelperSteps.advance (ActualLocalCopy.written f5 15 CopyCompilerFacts.destPointerLayout v6stage (.scalar dest)) ⟨7,5⟩
  have eqf6 : f6 = CopyHelperSteps.advance (ActualLocalCopy.written f5 15 CopyCompilerFacts.destPointerLayout v6stage (.scalar dest)) ⟨7,5⟩ := rfl
  clear_value f6
  have step6 : ExecutionMachine.step config limits () (Storage.withCurrent frames f5 machine) =
      (Storage.withCurrent frames f6 machine,.ok true) := by
    rw [eqf6]
    exact CopyHelperSteps.destination_copy_step options limits remaining span debugOff fuel validationFuel
      frames f5 machine dest (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using identity) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using callee)
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using (show (2 : MIR.LocalId) < frame.locals.size by rw [size];decide)) v6stage
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using live2) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using cached2)
      (by simp [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set]) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using uncached15)
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks) tracker tracked defaultMode ghost shallow (by simp [eqf1, eqf2, eqf3, eqf4, eqf5, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location])
  have v7stage : (16 : MIR.LocalId) < f6.locals.size := by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v16
  let f7 := SourceSteps.liveFrame f6 ⟨7,6⟩ 16 v7stage
  have eqf7 : f7 = SourceSteps.liveFrame f6 ⟨7,6⟩ 16 v7stage := rfl
  clear_value f7
  have step7 : ExecutionMachine.step config limits () (Storage.withCurrent frames f6 machine) =
      (Storage.withCurrent frames f7 machine,.ok true) := by
    rw [eqf7]
    exact CopyHelperSteps.storage_live options limits (remaining+1) span frames f6 machine ⟨7,6⟩ 16 5
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simp [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location]) (by decide +kernel) (by decide +kernel) (by decide +kernel) v7stage
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using dead16) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks)
  have v8stage : (16 : MIR.LocalId) < f7.locals.size := by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using v16
  let f8 := CopyHelperSteps.advance (ActualLocalCopy.written f7 16 RootCompilerFacts.usizeLayout v8stage (.scalar (.fromScalarInt (.ofUInt64 n)))) ⟨7,7⟩
  have eqf8 : f8 = CopyHelperSteps.advance (ActualLocalCopy.written f7 16 RootCompilerFacts.usizeLayout v8stage (.scalar (.fromScalarInt (.ofUInt64 n)))) ⟨7,7⟩ := rfl
  clear_value f8
  have step8 : ExecutionMachine.step config limits () (Storage.withCurrent frames f7 machine) =
      (Storage.withCurrent frames f8 machine,.ok true) := by
    rw [eqf8]
    exact CopyHelperSteps.count_copy_step options limits remaining span debugOff fuel validationFuel
      frames f7 machine n (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using sourceBody) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using identity) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using callee)
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using (show (3 : MIR.LocalId) < frame.locals.size by rw [size];decide)) v8stage
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using live3) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using cached3)
      (by simp [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set]) (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set] using uncached16)
      (by simpa [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using noClocks) tracker tracked defaultMode ghost shallow (by simp [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,location])
  have all1 : CopyHelperCleanup.AllImmediate f1 := by
    rw [eqf1]
    exact CopyHelperCleanup.all_immediate_set frame 5 _ v1stage allImmediate (by intro memory; simp)
  have all2 : CopyHelperCleanup.AllImmediate f2 := by
    rw [eqf2]
    exact CopyHelperCleanup.all_immediate_set f1 4 _ v2stage all1 (by intro memory; simp)
  have all3 : CopyHelperCleanup.AllImmediate f3 := by
    rw [eqf3]
    exact CopyHelperCleanup.all_immediate_set f2 14 _ v3stage all2 (by intro memory; simp)
  have all4 : CopyHelperCleanup.AllImmediate f4 := by
    rw [eqf4]
    exact CopyHelperCleanup.all_immediate_written f3 14 CopyCompilerFacts.sourcePointerLayout (.scalar source) v4stage all3
  have all5 : CopyHelperCleanup.AllImmediate f5 := by
    rw [eqf5]
    exact CopyHelperCleanup.all_immediate_set f4 15 _ v5stage all4 (by intro memory; simp)
  have all6 : CopyHelperCleanup.AllImmediate f6 := by
    rw [eqf6]
    exact CopyHelperCleanup.all_immediate_written f5 15 CopyCompilerFacts.destPointerLayout (.scalar dest) v6stage all5
  have all7 : CopyHelperCleanup.AllImmediate f7 := by
    rw [eqf7]
    exact CopyHelperCleanup.all_immediate_set f6 16 _ v7stage all6 (by intro memory; simp)
  have all8 : CopyHelperCleanup.AllImmediate f8 := by
    rw [eqf8]
    exact CopyHelperCleanup.all_immediate_written f7 16 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 n))) v8stage all7
  refine ⟨f1,f2,f3,f4,f5,f6,f7,f8,step1,step2,step3,step4,step5,step6,step7,step8,?_⟩
  simp only [all8, and_true]
  simp [eqf1, eqf2, eqf3, eqf4, eqf5, eqf6, eqf7, eqf8,SourceSteps.liveFrame,SourceSteps.deadFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set,Array.getElem?_set,size]

#print axioms actual_eight_statements
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_eight_statements) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperPreparation
