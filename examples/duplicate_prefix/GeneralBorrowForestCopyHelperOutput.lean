import duplicate_prefix.GeneralBorrowForestCopyHelperCall
import duplicate_prefix.MetadataOutputFacts
import duplicate_prefix.CopyHelperReturnDriver
namespace DuplicatePrefix.GeneralBorrowForestCopyHelperCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def memoryAfter (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (kind : MemoryKind MiriMemoryKind) (allocation : Allocation Provenance BorrowTree) : MemoryState Provenance BorrowTree MiriMemoryKind :=
  {memory with live := (memory.live.filter fun row => row.1 != id).push (id,⟨kind,allocation⟩)}
theorem memoryAfter_twice (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (kind : MemoryKind MiriMemoryKind) (first second : Allocation Provenance BorrowTree) :
    memoryAfter (memoryAfter memory id kind first) id kind second = memoryAfter memory id kind second := by
  simp [memoryAfter,Array.filter_filter]

theorem returns_to_caller_exact
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
    ∃ result finalMachine,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {PtrMetadataExecution.writeFrame caller callerId .uninit callerValid with location := .mir ⟨target,0⟩} finalMachine) ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,result⟩) ∧
      result.byteSize = allocation.byteSize ∧ result.len = allocation.len ∧ result.extra = writeAccess.tree ∧
      AllocationCopy.snapshot result = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧
      finalMachine.memory = memoryAfter machine.memory id kind result ∧
      finalMachine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
      finalMachine.dataRace = none ∧ finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      (config.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (config.terminators.getControl finalMachine.user).gcInterval = 0 ∧ finalMachine.threads.fixedScheduling = true ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨result,done,bodyTrace,bodyDone,identityDone,calleeDone,extraDone,returnDone,continuationDone,varargsDone,localsIdDone,
    sizeDone,locationDone,zeroDone,allDone,resultSize,resultLen,resultTree,resultBytes⟩ :=
    GeneralBorrowForestCopyHelperExecution.from_false_guard options limits remaining span sourceContract debugOff fuel validationFuel
      (frames.push caller) frame machine sourceBody identity callee location size tracker id tag base offset sliceLen n kind allocation
      positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached
      borrow bounded sourceLive destLive countLive sourceCached destCached countCached live4 uncached4 live5 cached5
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
  have finalUser : finalMachine.user = (PtrMetadataReturn.accountedMachine options remaining span copied).user := by
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  refine ⟨result,finalMachine,?_,?_,resultSize,resultLen,resultTree,resultBytes,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact SuccessfulTrace.append bodyTrace (.next returned (.refl _))
  · have memoryEq : finalMachine.memory = copied.memory := by
      unfold finalMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [memoryEq]
    exact CanonicalCopy.replace_lookup writeState id kind result
  · have memoryEq : finalMachine.memory = copied.memory := by
      unfold finalMachine GenericPopFrame.afterRelevanceAt
      split <;> rfl
    rw [memoryEq]
    change memoryAfter (memoryAfter (memoryAfter machine.memory id kind (allocation.setExtra readAccess.tree)) id kind
      ((allocation.setExtra readAccess.tree).setExtra writeAccess.tree)) id kind result = memoryAfter machine.memory id kind result
    rw [memoryAfter_twice,memoryAfter_twice]

  · unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  · change finalMachine.dataRace = none
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> exact noClocks
  · rw [finalUser,PtrMetadataReturn.accounted_ghost]
    exact ghostCopied
  · rw [finalUser,PtrMetadataReturn.accounted_validation]
    exact shallowCopied
  · rw [finalUser]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at uncheckedCopied ⊢
    exact uncheckedCopied
  · rw [finalUser]
    unfold PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at noGcCopied ⊢
    exact noGcCopied
  · unfold finalMachine GenericPopFrame.afterRelevanceAt
    split <;> exact fixed
  · rw [finalUser]
    change (PtrMetadataReturn.accountedMachine options remaining span clock2).user.addresses = machine.user.addresses
    unfold clock2 clock1 CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  · rw [finalUser]
    change (PtrMetadataReturn.accountedMachine options remaining span clock2).user.payload.payload.user.types = machine.user.payload.payload.user.types
    unfold clock2 clock1 CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  · rw [finalUser]
    change (PtrMetadataReturn.accountedMachine options remaining span clock2).user.payload.payload.user.backend = machine.user.payload.payload.user.backend
    unfold clock2 clock1 CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  · rw [finalUser]
    change (PtrMetadataReturn.accountedMachine options remaining span clock2).user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras
    unfold clock2 clock1 CopyHelperClock.advance PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  · let released := ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span copied) copied.memory tracker borrowFrame
    have known : released.threads.activeThread? = some thread := active
    unfold finalMachine GenericPopFrame.afterRelevanceAt
    split
    · exact ⟨_,MetadataOutputFacts.relevance_active (frames.push caller) cachedDone released thread known⟩
    · exact ⟨thread,known⟩

#print axioms returns_to_caller_exact
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``returns_to_caller_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.GeneralBorrowForestCopyHelperCall
