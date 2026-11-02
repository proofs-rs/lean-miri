import duplicate_prefix.CopyHelperPreparation
import duplicate_prefix.GeneralBorrowFreshRootScopedCopyHelperMemory
import duplicate_prefix.CopyHelperCleanup
import duplicate_prefix.SuccessfulTrace
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedCopyHelperBody
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
    (borrow : GeneralBorrowFreshRootScopedCopyInput.Input allocation.extra tracker.global tag offset sliceLen n)

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
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len := by
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
  obtain ⟨result,memoryStep,resultSize,resultLen,resultTree,resultBytes⟩ :=
    GeneralBorrowFreshRootScopedCopyHelperMemory.actual_initialized_copy_step options limits (remaining+1) span debugOff frames f8 machine
      (body8.trans sourceBody) location8 tracker id tag base offset sliceLen n kind allocation positive sliceBounds copyBounds
      storage maskValid maskLen initialized valid storageFits mutable noClocks noBackend tracked extras live cached borrow
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
    localsIdDone.trans localsId8,sizeDone,locationDone,zeroDone.trans zero8,allDone,resultSize,resultLen,resultTree,resultBytes⟩
  exact .next step1 (.next step2 (.next step3 (.next step4 (.next step5 (.next step6 (.next step7 (.next step8
    (.next memoryStep (.next step9 (.next step10 (.next step11 (.refl _))))))))))))

#print axioms to_return
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``to_return) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.GeneralBorrowFreshRootScopedCopyHelperBody
