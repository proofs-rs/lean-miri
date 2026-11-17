import duplicate_prefix.RootPrefix
import duplicate_prefix.RootCopyCount
import duplicate_prefix.RootEqStepSuccess

/-! Five actual source steps through the first block: three StorageLive
statements, the count Copy, and the zero guard Eq assignment. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootBlock0
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem actual_first_block_statements
    [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (n : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (location : frame.location = .mir ⟨0,0⟩)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (size : frame.locals.size = 25)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (dead5 : (frame.locals[5]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (uncached5 : (frame.locals[5]'(by omega)).layout = none)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (live2 : (frame.locals[2]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = Miri.TreeBorrows.RetagPolicy.RetagMode.Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (fuel : Nat) (fuelEq : options.limits.validation = fuel + 1) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    ∃ first second third fourth fifth,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) = (first, .ok true) ∧
      ExecutionMachine.step config limits () first = (second, .ok true) ∧
      ExecutionMachine.step config limits () second = (third, .ok true) ∧
      ExecutionMachine.step config limits () third = (fourth, .ok true) ∧
      ExecutionMachine.step config limits () fourth = (fifth, .ok true) ∧
      third = Storage.withCurrent framesBefore (RootPrefix.afterStorageFrame frame size) machine ∧
      fifth = Storage.withCurrent framesBefore
        (RootEqStepSuccess.postFrame (RootCopyCount.postFrame
          (RootPrefix.afterStorageFrame frame size)
          (by simp [RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size]) n)
          (by simp [RootCopyCount.postFrame, RootCopyCount.writeFrame,
            RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size,
            LocalPlaces.cachePlaceLayout]) n) machine ∧
      (fifth.stack.currentFrame?.map (·.location)) = some (.mir ⟨0,5⟩) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let afterStorage := RootPrefix.afterStorageFrame frame size
  obtain ⟨first, second, third, firstStep, secondStep, thirdStep, thirdEq, thirdMachine, thirdLoc⟩ :=
    RootPrefix.actual_initial_storage options (remaining + 1) span limits framesBefore frame machine
      body location size dead3 dead4 dead5 noClocks
  have storageShape := RootPrefix.after_storage_shape frame size
  rcases storageShape with ⟨bodyStorage, identityStorage, calleeStorage, extraStorage, sizeStorage, locationStorage⟩
  have valid2Storage : (2 : Miri.MIR.LocalId) < afterStorage.locals.size := by
    simp [afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size]
  have live2Storage : (afterStorage.locals[2]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))) := by
    have slot := RootPrefix.after_storage_slot2 frame size
    have valueEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.value) slot
    simpa [afterStorage] using valueEq.trans live2
  have cached2Storage : (afterStorage.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout := by
    have slot := RootPrefix.after_storage_slot2 frame size
    have layoutEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.layout) slot
    simpa [afterStorage] using layoutEq.trans cached2
  have valid4Storage : (4 : Miri.MIR.LocalId) < afterStorage.locals.size := by
    simp [afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size]
  have uninit4Storage : (afterStorage.locals[4]'(by omega)).value = .live (.immediate .uninit) := by
    have slot := RootPrefix.after_storage_slot4 frame size
    have valueEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.value) slot
    simpa [afterStorage] using valueEq
  have uncached4Storage : (afterStorage.locals[4]'(by omega)).layout = none := by
    have slot := RootPrefix.after_storage_slot4 frame size
    have layoutEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.layout) slot
    simpa [afterStorage] using layoutEq.trans uncached4
  have valid5Storage : (5 : Miri.MIR.LocalId) < afterStorage.locals.size := by
    simp [afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size]
  have uninit5Storage : (afterStorage.locals[5]'(by omega)).value = .live (.immediate .uninit) := by
    have slot := RootPrefix.after_storage_slot5 frame size
    have valueEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.value) slot
    simpa [afterStorage] using valueEq
  have uncached5Storage : (afterStorage.locals[5]'(by omega)).layout = none := by
    have slot := RootPrefix.after_storage_slot5 frame size
    have layoutEq := congrArg (fun slot : LocalState Provenance LocalLayout => slot.layout) slot
    simpa [afterStorage] using layoutEq.trans uncached5
  have noClocksStorage : afterStorage.extra.dataRace = none := by
    simpa [afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame] using noClocks
  have countStep := RootCopyCount.actual_copy_count_step options limits remaining span debugOff
    framesBefore afterStorage machine n valid2Storage live2Storage cached2Storage valid5Storage
    uninit5Storage uncached5Storage noClocksStorage
    (by rw [bodyStorage, body]) (by rw [identityStorage, identity]) locationStorage
    (by rw [calleeStorage, callee]) tracker tracked defaultMode ghostFalse shallow fuel fuelEq
  let countFrame := RootCopyCount.postFrame afterStorage valid5Storage n
  let fourth := Storage.withCurrent framesBefore countFrame machine
  have fourthEq : fourth = Storage.withCurrent framesBefore countFrame machine := rfl
  have countFrameSize : countFrame.locals.size = afterStorage.locals.size := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame,
      LocalPlaces.cachePlaceLayout, Array.size_set]
  have valid4Count : (4 : Miri.MIR.LocalId) < countFrame.locals.size := by
    rw [countFrameSize]
    exact valid4Storage
  have uninit4Count : (countFrame.locals[4]'(by omega)).value = .live (.immediate .uninit) := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame,
      afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size,
      LocalPlaces.cachePlaceLayout]
  have uncached4Count : (countFrame.locals[4]'(by omega)).layout = none := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame,
      afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size, uncached4,
      LocalPlaces.cachePlaceLayout]
  have valid5Count : (5 : Miri.MIR.LocalId) < countFrame.locals.size := by
    rw [countFrameSize]
    exact valid5Storage
  have live5Count : (countFrame.locals[5]'(by omega)).value = .live
      (.immediate (.scalar (.fromScalarInt (ScalarInt.ofUInt64 n)))) := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame,
      afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size,
      LocalPlaces.cachePlaceLayout]
  have cached5Count : (countFrame.locals[5]'(by omega)).layout = some RootCompilerFacts.usizeLayout := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame,
      afterStorage, RootPrefix.afterStorageFrame, SourceSteps.liveFrame, size,
      LocalPlaces.cachePlaceLayout]
  have noClocksCount : countFrame.extra.dataRace = none := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame, afterStorage,
      RootPrefix.afterStorageFrame, SourceSteps.liveFrame, noClocks,
      LocalPlaces.cachePlaceLayout]
  have bodyCount : countFrame.body = RootBody.reflected.body.body := by
    simpa [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame, afterStorage,
      LocalPlaces.cachePlaceLayout] using bodyStorage.trans body
  have identityCount : countFrame.bodyIdentity = RootBody.reflected.body.identity := by
    simpa [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame, afterStorage,
      LocalPlaces.cachePlaceLayout] using identityStorage.trans identity
  have locationCount : countFrame.location = .mir ⟨0,4⟩ := by
    simp [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame, afterStorage,
      RootPrefix.afterStorageFrame, SourceSteps.liveFrame]
  have calleeCount : countFrame.functionInstance = RootBody.reflected.functionInstance := by
    simpa [countFrame, RootCopyCount.postFrame, RootCopyCount.writeFrame, afterStorage,
      LocalPlaces.cachePlaceLayout] using calleeStorage.trans callee
  have eqStep := RootEqStepSuccess.actual_root_eq_step_succeeds options limits remaining span
    source debugOff framesBefore countFrame machine n
    valid4Count uncached4Count uninit4Count valid5Count live5Count cached5Count noClocksCount
    bodyCount identityCount locationCount calleeCount ghostFalse shallow fuel fuelEq
  refine ⟨first, second, third, fourth,
    Storage.withCurrent framesBefore (RootEqStepSuccess.postFrame countFrame valid4Count n) machine,
    firstStep, secondStep, thirdStep, ?_, ?_, thirdEq, ?_, ?_⟩
  · rw [thirdEq]
    simpa [fourth, countFrame, RootCopyCount.postFrame, afterStorage] using countStep
  · exact eqStep
  · rfl
  · simp [Stack.currentFrame?, RootEqStepSuccess.postFrame, countFrame, RootCopyCount.postFrame,
      RootCopyCount.writeFrame, afterStorage, RootPrefix.afterStorageFrame,
      SourceSteps.liveFrame, Storage.withCurrent, LocalPlaces.cachePlaceLayout]

#print axioms actual_first_block_statements
end DuplicatePrefix.RootBlock0
