import duplicate_prefix.EmptyForestPoolSafetyToLen
import duplicate_prefix.S03EmptySharedRuntime

namespace DuplicatePrefix.S03EmptySharedPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootReferenceInfo
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual positive-count empty body from entry through its Shared
expression to the len call retains the caller's general return window and
original empty-tag quiescence. No Default/as_mut_ptr branch is executed. -/
theorem with_observer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (parentTag newTag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset count : UInt64) (nonzero : base+offset≠0) (countNonzero : count≠0)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (cache4 : (frame.locals[4]'(by omega)).layout=none) (cache5 : (frame.locals[5]'(by omega)).layout=none)
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false)
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (ownerSource ownerSelected : Option UniIndex) (ownerMaximum : Option BorTag)
    (ownerOffset ownerLen : UInt64)
    (ownerPositive : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      ownerSource ownerSelected ownerMaximum ownerOffset ownerLen)
    (owner : UniIndex)
    (ownerActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra owner .Write ownerOffset (ownerOffset+ownerLen))
    (zero : UniIndex) (zeroQuiet : S04ReturnReleaseInactive.Quiescent entry.allocation.extra zero) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ result : CompilerFrameContext.ActualFrame,
      (      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result ({ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span machine) tracker fresh with
          memory := RetagEntry.updatedMemory machine.memory id entry input.after})) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.returnPlace=frame.returnPlace ∧ result.returnContinuation=frame.returnContinuation ∧
      result.vaList=frame.vaList ∧ result.localsIdentity=frame.localsIdentity ∧ result.locals.size=25 ∧ result.location=.mir ⟨2,12⟩ ∧
      result.locals[0]?=frame.locals[0]? ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[7]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[8]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[9]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.locals[10]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[11]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[12]?=some ⟨.live (.immediate (RetagReferencePlace.sliceValue
      (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id newTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ ∧
      result.locals[13]?=frame.locals[13]? ∧ CopyHelperCleanup.AllImmediate result ) ∧
      let finalGlobal := GeneralBorrowFnEntryRegistration.advanced tracker.global fresh
      DuplicatePrefixBorrowContract.RuntimeFacts input.after finalGlobal ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive input.after finalGlobal.protectedTags
        ownerSource ownerSelected ownerMaximum ownerOffset ownerLen) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin input.after owner .Write ownerOffset (ownerOffset+ownerLen) ∧
      S04ReturnReleaseInactive.Quiescent input.after zero := by
  cases nextTag
  have borrow := S03EmptySharedRuntime.allocate_construct entry.allocation.extra tracker.global borrowRuntime parentTag input
    nodeRoom fresh offset ownerSource ownerSelected ownerMaximum ownerOffset ownerLen ownerPositive owner ownerActive zero zeroQuiet
  obtain ⟨result,original⟩ := EmptyForestPoolSafetyToLen.executes
    options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
    frame machine parentTag tracker.global.nextPointerTag id entry base offset count nonzero countNonzero input size
    source1 cache1 live2 cache2 dead3 cache3 dead4 dead5 cache4 cache5 unused body identity callee location noClocks all
    tracker tracked mode rfl fresh cachedAddress present ghost shallow unchecked noGc fixed metadata notConstructed
  exact ⟨result,original,borrow.2.2.1,borrow.2.2.2.1,borrow.2.2.2.2.1,borrow.2.2.2.2.2⟩

end DuplicatePrefix.S03EmptySharedPrefix
