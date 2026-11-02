import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.CopyHelperCleanup
import duplicate_prefix.CopyHelperClock
import duplicate_prefix.CopyHelperPreparation
import duplicate_prefix.CopyHelperReturnDriver
import duplicate_prefix.CopyHelperUnitBlock
import duplicate_prefix.CurrentCallPhysicalCopy
import duplicate_prefix.SuccessfulTrace

/-! Actual copy-helper execution and empty-frame return from internal completed
Read/sequential Write certificates and current window-local physical metadata. -/
namespace DuplicatePrefix.CurrentCallCopyHelperExecution
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,0⟩)
    (size : frame.locals.size = 17)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (readReady : CurrentCallBoolProtection.WindowReady machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady machine id (offset+n).toNat n.toNat)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (readCompleted : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (sequentialWriteCompleted : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)

    (bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceLive : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (destLive : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (countLive : (frame.locals[3]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (sourceCached : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.sourcePointerLayout)
    (destCached : (frame.locals[2]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countCached : (frame.locals[3]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
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
    (localClocks : frame.extra.dataRace = none)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let state := Storage.withCurrent frames frame machine
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result done,
      SuccessfulTrace.Trace config limits state
        (Storage.withCurrent frames done (CanonicalCopy.replaceAllocation writeState id kind result).machine) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧ done.locals.size = 17 ∧
      done.location = .mir ⟨7,12⟩ ∧ done.locals[0]? = frame.locals[0]? ∧ CopyHelperCleanup.AllImmediate done ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧ S02SameDestinationAcceptedCopyPhysical.Physical result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let source : Scalar Provenance := Scalar.fromPointer config.access.runtime.base (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  let dest : Scalar Provenance := Scalar.fromPointer config.access.runtime.base (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+(offset+n))))
  obtain ⟨f1,f2,f3,f4,f5,f6,f7,f8,step1,step2,step3,step4,step5,step6,step7,step8,
    body8,identity8,callee8,extra8,return8,continuation8,varargs8,localsId8,size8,location8,zero8,all8,
    source8,dest8,count8⟩ := CopyHelperPreparation.actual_eight_statements options limits remaining span debugOff fuel validationFuel
      frames frame machine source dest n size sourceBody identity callee location sourceLive sourceCached destLive destCached
      countLive countCached live4 cached4 live5 cached5 dead14 uncached14 dead15 uncached15 dead16 uncached16
      allImmediate localClocks tracker tracked defaultMode ghost shallow
  have v14 : (14 : MIR.LocalId) < f8.locals.size := by rw [size8];decide
  have v15 : (15 : MIR.LocalId) < f8.locals.size := by rw [size8];decide
  have v16 : (16 : MIR.LocalId) < f8.locals.size := by rw [size8];decide
  have source8' : f8.locals[14] = ⟨.live (.immediate (.scalar source)),some CopyCompilerFacts.sourcePointerLayout⟩ :=
    Option.some.inj ((getElem?_pos f8.locals 14 v14).symm.trans source8)
  have dest8' : f8.locals[15] = ⟨.live (.immediate (.scalar dest)),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((getElem?_pos f8.locals 15 v15).symm.trans dest8)
  have count8' : f8.locals[16] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((getElem?_pos f8.locals 16 v16).symm.trans count8)
  obtain ⟨result,memoryStep,resultSize,resultLen,resultTree,resultBytes,resultPhysical⟩ :=
    CurrentCallPhysicalCopy.actual_initialized_copy_step options limits (remaining+1) span debugOff frames f8 machine
      (body8.trans sourceBody) location8 tracker id tag base offset sliceLen n kind allocation positive sliceBounds copyBounds
      storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked readReady writeReady live cached readCompleted sequentialWriteCompleted
      bounded v14 v15 v16 (congrArg LocalState.value source8') (congrArg LocalState.value dest8')
      (congrArg LocalState.value count8') (congrArg LocalState.layout source8') (congrArg LocalState.layout dest8')
      (congrArg LocalState.layout count8') (extra8 ▸ localClocks) ghost
  let state := Storage.withCurrent frames frame machine
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
  let afterMachine := (CanonicalCopy.replaceAllocation writeState id kind result).machine
  let afterFrame := {f8 with location := .mir ⟨7,9⟩}
  have beforeStack : (CanonicalCopy.replaceAllocation
      (CanonicalCopy.replaceAllocation
        (CanonicalCopy.replaceAllocation (Storage.withCurrent frames f8 machine) id kind (allocation.setExtra readAccess.tree))
        id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)) id kind result).machine = afterMachine := rfl
  change ExecutionMachine.step config limits () (Storage.withCurrent frames f8 machine) =
    (Storage.withCurrent frames afterFrame afterMachine,.ok true) at memoryStep
  obtain ⟨f9,f10,done,step9,step10,step11,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,
    varargsDone,localsIdDone,sizeDone,locationDone,zeroDone,allDone⟩ :=
      CopyHelperCleanup.actual_three_dead options limits (remaining+1) span frames afterFrame afterMachine source dest n
        size8 (body8.trans sourceBody) rfl (congrArg LocalState.value source8') (congrArg LocalState.value dest8')
        (congrArg LocalState.value count8') all8
  refine ⟨result,done,?_,bodyDone.trans body8,identityDone.trans identity8,calleeDone.trans callee8,
    extraDone.trans extra8,returnDone.trans return8,continuationDone.trans continuation8,varargsDone.trans varargs8,
    localsIdDone.trans localsId8,sizeDone,locationDone,zeroDone.trans zero8,allDone,resultSize,resultLen,resultTree,resultBytes,resultPhysical⟩
  exact .next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.next step6 (.next step7 (.next step8
    (.next memoryStep (.next step9 (.next step10 (.next step11 (.refl _))))))))))))

end DuplicatePrefix.CurrentCallCopyHelperExecution

namespace DuplicatePrefix.CurrentCallCopyHelperExecution
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem from_false_guard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sourceContract : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨1,0⟩)
    (size : frame.locals.size = 17)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (readReady : CurrentCallBoolProtection.WindowReady machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady machine id (offset+n).toNat n.toNat)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (readCompleted : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (sequentialWriteCompleted : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)

    (bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceLive : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (destLive : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (countLive : (frame.locals[3]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (sourceCached : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.sourcePointerLayout)
    (destCached : (frame.locals[2]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countCached : (frame.locals[3]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate (.scalar (.fromBool false))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (uncached14 : (frame.locals[14]'(by omega)).layout = none)
    (dead15 : (frame.locals[15]'(by omega)).value = .dead)
    (uncached15 : (frame.locals[15]'(by omega)).layout = none)
    (dead16 : (frame.locals[16]'(by omega)).value = .dead)
    (uncached16 : (frame.locals[16]'(by omega)).layout = none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (localClocks : frame.extra.dataRace = none)
    (defaultMode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let clock2 := CopyHelperClock.advance options remaining span (CopyHelperClock.advance options remaining span machine)
    let state := Storage.withCurrent frames frame clock2
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result done,
      SuccessfulTrace.Trace config limits (Storage.withCurrent frames frame machine)
        (Storage.withCurrent frames done (CanonicalCopy.replaceAllocation writeState id kind result).machine) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧ done.functionInstance = frame.functionInstance ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧ done.locals.size = 17 ∧
      done.location = .mir ⟨7,12⟩ ∧ done.locals[0]? = frame.locals[0]? ∧ CopyHelperCleanup.AllImmediate done ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧ S02SameDestinationAcceptedCopyPhysical.Physical result := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let clock1 := CopyHelperClock.advance options remaining span machine
  let clock2 := CopyHelperClock.advance options remaining span clock1
  let bb6 := {frame with location := .mir ⟨6,0⟩}
  have valid4 : (4 : MIR.LocalId) < bb6.locals.size := by change 4 < frame.locals.size; rw [size];decide
  let written := CopyHelperSteps.advance (ActualLocalCopy.written bb6 4 CopyHelperUnit.layout valid4 .uninit) ⟨6,0⟩
  let bb7 := {written with location := .mir ⟨7,0⟩}
  have valid5 : (5 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have branch := CopyHelperControl.false_switch_step options limits remaining span debugOff frames frame machine
    sourceBody location valid5 live5 cached5 localClocks unchecked noGc fixed ghost
  have unchecked1 : (config.terminators.getControl clock1.user).checkedArithmetic = false := by
    rw [CopyHelperClock.control]
    exact unchecked
  have noGc1 : (config.terminators.getControl clock1.user).gcInterval = 0 := by
    rw [CopyHelperClock.control]
    exact noGc
  have unitSteps := CopyHelperUnitBlock.actual_two_steps options limits remaining span
    sourceContract debugOff fuel validationFuel
    frames bb6 clock1 .uninit valid4 live4 uncached4 sourceBody identity rfl callee localClocks
    tracker tracked defaultMode unchecked1 noGc1 fixed
    (by rw [PtrMetadataReturn.accounted_ghost];exact ghost)
    (by rw [PtrMetadataReturn.accounted_validation];exact shallow)
  have bb7SourceBody : bb7.body = HelperCompilerFacts.copyBody.body := sourceBody
  have bb7Size : bb7.locals.size = 17 := by simp [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,size]
  have bb7Source : (bb7.locals[1]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer config.access.runtime.base (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))) := by
    simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using sourceLive
  have clock2Backend : clock2.user.payload.payload.user.backend = .none := by
    rw [CopyHelperClock.backend,CopyHelperClock.backend];exact noBackend
  have clock2ReadReady : CurrentCallBoolProtection.WindowReady clock2 id offset.toNat n.toNat :=
    readReady.transport (by rw [CopyHelperClock.runtime,CopyHelperClock.runtime])
  have clock2WriteReady : CurrentCallBoolProtection.WindowReady clock2 id (offset+n).toNat n.toNat :=
    writeReady.transport (by rw [CopyHelperClock.runtime,CopyHelperClock.runtime])
  have clock2Cached : clock2.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [CopyHelperClock.addresses,CopyHelperClock.addresses];exact cached
  have allBb6 : CopyHelperCleanup.AllImmediate bb6 := allImmediate
  have allWritten : CopyHelperCleanup.AllImmediate written := CopyHelperCleanup.all_immediate_written bb6 4 CopyHelperUnit.layout .uninit valid4 allBb6
  have allBb7 : CopyHelperCleanup.AllImmediate bb7 := allWritten
  obtain ⟨result,done,trace,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,
    sizeDone,locationDone,zeroDone,allDone,resultSize,resultLen,resultTree,resultBytes,resultPhysical⟩ :=
    CurrentCallCopyHelperExecution.to_return options limits remaining span debugOff fuel validationFuel frames bb7 clock2
      bb7SourceBody identity callee rfl bb7Size tracker id tag base offset sliceLen n kind allocation positive sliceBounds copyBounds
      storage maskValid maskLen initialized valid storageFits mutable noClocks clock2Backend tracked clock2ReadReady clock2WriteReady live clock2Cached readCompleted sequentialWriteCompleted bounded
      bb7Source
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using destLive)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using countLive)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using sourceCached)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using destCached)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using countCached)
      (by simp [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6])
      (by simp [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6])
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using live5)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using cached5)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using dead14)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using uncached14)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using dead15)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using uncached15)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using dead16)
      (by simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem_set] using uncached16)
      allBb7 localClocks defaultMode
      (by rw [PtrMetadataReturn.accounted_ghost,PtrMetadataReturn.accounted_ghost];exact ghost)
      (by rw [PtrMetadataReturn.accounted_validation,PtrMetadataReturn.accounted_validation];exact shallow)
  refine ⟨result,done,?_,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,sizeDone,locationDone,?_,allDone,resultSize,resultLen,resultTree,resultBytes,resultPhysical⟩
  · exact .next branch (.next unitSteps.1 (.next unitSteps.2 trace))
  · simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem?_set] using zeroDone

end DuplicatePrefix.CurrentCallCopyHelperExecution

namespace DuplicatePrefix.CurrentCallCopyHelperExecution
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem returns_to_caller
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (sourceContract : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨1,0⟩)
    (size : frame.locals.size = 17)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (tag : BorTag)
    (base offset sliceLen n : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask
      (Size.ofBytes offset) (Size.ofBytes (offset + n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (readReady : CurrentCallBoolProtection.WindowReady machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady machine id (offset+n).toNat n.toNat)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (readCompleted : (allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (sequentialWriteCompleted : ((allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)

    (bounded : n ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceLive : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (destLive : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+(offset+n))))))))
    (countLive : (frame.locals[3]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (sourceCached : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.sourcePointerLayout)
    (destCached : (frame.locals[2]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (countCached : (frame.locals[3]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live4 : (frame.locals[4]'(by omega)).value = .live (.immediate .uninit))
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (live5 : (frame.locals[5]'(by omega)).value = .live (.immediate (.scalar (.fromBool false))))
    (cached5 : (frame.locals[5]'(by omega)).layout = some RootCompilerFacts.boolLayout)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (uncached14 : (frame.locals[14]'(by omega)).layout = none)
    (dead15 : (frame.locals[15]'(by omega)).value = .dead)
    (uncached15 : (frame.locals[15]'(by omega)).layout = none)
    (dead16 : (frame.locals[16]'(by omega)).value = .dead)
    (uncached16 : (frame.locals[16]'(by omega)).layout = none)
    (allImmediate : CopyHelperCleanup.AllImmediate frame)
    (localClocks : frame.extra.dataRace = none)
    (defaultMode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (zeroLive : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (zeroUncached : (frame.locals[0]'(by omega)).layout = none)
    (varargs : frame.vaList = #[])
    (borrowFrame : FrameState) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    let clock2 := CopyHelperClock.advance options remaining span (CopyHelperClock.advance options remaining span machine)
    let state := Storage.withCurrent (frames.push caller) frame clock2
    let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
    let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {PtrMetadataExecution.writeFrame caller callerId .uninit callerValid with location := .mir ⟨target,0⟩} finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,result⟩) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧ S02SameDestinationAcceptedCopyPhysical.Physical result ∧
      finalMachine.memory = (CanonicalCopy.replaceAllocation writeState id kind result).machine.memory ∧
      finalMachine.borrowTracker = some tracker ∧
      finalMachine.user = (CopyHelperClock.advance options remaining span clock2).user ∧
      finalMachine.dataRace = machine.dataRace ∧
      finalMachine.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨result,done,bodyTrace,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,
    sizeDone,locationDone,zeroDone,allDone,resultSize,resultLen,resultTree,resultBytes,resultPhysical⟩ :=
    CurrentCallCopyHelperExecution.from_false_guard options limits remaining span sourceContract debugOff fuel validationFuel
      (frames.push caller) frame machine sourceBody identity callee location size tracker id tag base offset sliceLen n kind allocation
      positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked readReady writeReady live cached
      readCompleted sequentialWriteCompleted bounded sourceLive destLive countLive sourceCached destCached countCached live4 uncached4 live5 cached5
      dead14 uncached14 dead15 uncached15 dead16 uncached16 allImmediate localClocks defaultMode unchecked noGc fixed ghost shallow
  let clock1 := CopyHelperClock.advance options remaining span machine
  let clock2 := CopyHelperClock.advance options remaining span clock1
  let state := Storage.withCurrent (frames.push caller) frame clock2
  let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes offset) (Size.ofBytes n) .Read tracker.global.protectedTags .VisitChildrenOfAccessed
  let readState := CanonicalCopy.replaceAllocation state id kind (allocation.setExtra readAccess.tree)
  let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let writeState := CanonicalCopy.replaceAllocation readState id kind ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)
  let copied := (CanonicalCopy.replaceAllocation writeState id kind result).machine
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [sizeDone];decide
  have oldValid0 : (0 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have oldNode : frame.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by
    cases slot : frame.locals[0] with
    | mk value layout =>
      have lv : value = .live (.immediate .uninit) := by simpa only [slot] using zeroLive
      have lc : layout = none := by simpa only [slot] using zeroUncached
      simp only [lv,lc]
  have zeroNode : done.locals[0] = ⟨.live (.immediate .uninit),none⟩ := by
    apply Option.some.inj
    rw [← getElem?_pos done.locals 0 valid0,zeroDone,getElem?_pos frame.locals 0 oldValid0,oldNode]
  have allCached : ∀ slot ∈ (LocalOperands.cachedLayoutFrame done 0 CopyHelperUnit.layout valid0).locals,
      ∀ memory, slot.value ≠ .live (.indirect memory) :=
    CopyHelperCleanup.all_immediate_cache done 0 CopyHelperUnit.layout valid0 allDone
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList copied.memory copied.memory := by
    rw [empty]
    exact .nil _
  have uncheckedCopied : (config.terminators.getControl copied.user).checkedArithmetic = false := by
    change (config.terminators.getControl clock2.user).checkedArithmetic = false
    rw [CopyHelperClock.control,CopyHelperClock.control]
    exact unchecked
  have noGcCopied : (config.terminators.getControl copied.user).gcInterval = 0 := by
    change (config.terminators.getControl clock2.user).gcInterval = 0
    rw [CopyHelperClock.control,CopyHelperClock.control]
    exact noGc
  have ghostCopied : copied.user.payload.ghost = false := by
    change clock2.user.payload.ghost = false
    rw [PtrMetadataReturn.accounted_ghost,PtrMetadataReturn.accounted_ghost]
    exact ghost
  have shallowCopied : copied.user.payload.validation = .Shallow := by
    change clock2.user.payload.validation = .Shallow
    rw [PtrMetadataReturn.accounted_validation,PtrMetadataReturn.accounted_validation]
    exact shallow
  have returned := CopyHelperReturnDriver.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done copied (bodyDone.trans sourceBody) (identityDone.trans identity) (calleeDone.trans callee)
    locationDone valid0 (congrArg LocalState.value zeroNode) (congrArg LocalState.layout zeroNode)
    (by rw [extraDone];exact localClocks) callerId callerValid callerOld callerLive callerCached callerClocks
    (by rw [returnDone];exact destination) target unwindAction (by rw [continuationDone];exact continuation)
    allCached (by rw [varargsDone];exact varargs) tracker borrowFrame tracked (by rw [extraDone];exact frameTracked)
    copied.memory plan thread active uncheckedCopied noGcCopied fixed ghostCopied shallowCopied
  let cachedDone := LocalOperands.cachedLayoutFrame done 0 CopyHelperUnit.layout valid0
  let finalMachine := GenericPopFrame.afterRelevanceAt (frames.push caller) cachedDone
    (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span copied) copied.memory tracker borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  have memoryEq : finalMachine.memory = copied.memory := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have finalTracked : finalMachine.borrowTracker = some tracker := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> simp only [ActualPopPlan.released,GlobalState.endCall,empty,Array.foldl_empty]
    all_goals rfl
  have finalUser : finalMachine.user = (CopyHelperClock.advance options remaining span clock2).user := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have finalRace : finalMachine.dataRace = machine.dataRace := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have finalFixed : finalMachine.threads.fixedScheduling = machine.threads.fixedScheduling := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have finalActive : ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
    let released := ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span copied) copied.memory tracker borrowFrame
    have actor : released.threads.activeThread? = some thread := active
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split
    · exact ⟨_,MetadataOutputFacts.relevance_active (frames.push caller) cachedDone released thread actor⟩
    · exact ⟨thread,actor⟩
  refine ⟨result,finalMachine,?_,?_,resultSize,resultLen,resultTree,resultBytes,resultPhysical,memoryEq,finalTracked,finalUser,finalRace,finalFixed,finalActive⟩
  · exact SuccessfulTrace.append bodyTrace (.next returned (.refl _))
  · have memoryEq : finalMachine.memory = copied.memory := by
      unfold finalMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [memoryEq]
    exact CanonicalCopy.replace_lookup writeState id kind result

end DuplicatePrefix.CurrentCallCopyHelperExecution

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallCopyHelperExecution." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current copy helper dependency {dependency}"
