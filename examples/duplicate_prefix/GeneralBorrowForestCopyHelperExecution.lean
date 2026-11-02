import duplicate_prefix.GeneralBorrowForestCopyHelperBody
import duplicate_prefix.CopyHelperUnitBlock
import duplicate_prefix.CopyHelperClock
namespace DuplicatePrefix.GeneralBorrowForestCopyHelperExecution
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
    (valid : ProvenanceCopy.WellFormed allocation.provenanceMap allocation.len)
    (storageFits : allocation.len + 64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩))
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id, ⟨kind, allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (borrow : GeneralBorrowForestCopyInput.Input allocation.extra tracker.global.protectedTags tag offset sliceLen n)

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
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len := by
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
  have clock2Extras : clock2.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩) := by
    rw [CopyHelperClock.runtime,CopyHelperClock.runtime];exact extras
  have clock2Cached : clock2.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [CopyHelperClock.addresses,CopyHelperClock.addresses];exact cached
  have allBb6 : CopyHelperCleanup.AllImmediate bb6 := allImmediate
  have allWritten : CopyHelperCleanup.AllImmediate written := CopyHelperCleanup.all_immediate_written bb6 4 CopyHelperUnit.layout .uninit valid4 allBb6
  have allBb7 : CopyHelperCleanup.AllImmediate bb7 := allWritten
  obtain ⟨result,done,trace,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,
    sizeDone,locationDone,zeroDone,allDone,resultSize,resultLen,resultTree,resultBytes⟩ :=
    GeneralBorrowForestCopyHelperBody.to_return options limits remaining span debugOff fuel validationFuel frames bb7 clock2
      bb7SourceBody identity callee rfl bb7Size tracker id tag base offset sliceLen n kind allocation positive sliceBounds copyBounds
      storage maskValid maskLen initialized valid storageFits mutable noClocks clock2Backend tracked clock2Extras live clock2Cached borrow bounded
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
  refine ⟨result,done,?_,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,sizeDone,locationDone,?_,allDone,resultSize,resultLen,resultTree,resultBytes⟩
  · exact .next branch (.next unitSteps.1 (.next unitSteps.2 trace))
  · simpa [bb7,written,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,bb6,Array.getElem?_set] using zeroDone

#print axioms from_false_guard
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``from_false_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.GeneralBorrowForestCopyHelperExecution
