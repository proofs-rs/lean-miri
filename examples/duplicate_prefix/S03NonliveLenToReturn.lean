import duplicate_prefix.S03NonliveLenCall
import duplicate_prefix.GeneralBorrowRawLenRejectedFrame
import duplicate_prefix.PositiveLenPost

namespace DuplicatePrefix.S03NonliveLenToReturn
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend LenCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual nonlive empty len call, its protector pop and rejecting-body steps
reach block10 with complete caller memory and physical metadata preserved. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (metadataTag : Option BorTag) (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (nonliveMetadata : DuplicatePrefixEmptyReferenceInput.Metadata beforeMachine.memory id metadataTag)
    (absent : beforeMachine.memory.live.find? (fun row => row.1 == id) = none)
    (cachedAddress : beforeMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : beforeMachine.user.payload.ghost = false) (shallow : beforeMachine.user.payload.validation = .Shallow)
    (race : beforeMachine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : beforeMachine.threads.activeThread? = some thread)
    (cachedThread : thread.topUserRelevantFrame = some 0)
    (metadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (count : UInt64) (countNonzero : count ≠ 0) (frameSize : caller.locals.size = 25)
    (allImmediate : CopyHelperCleanup.AllImmediate caller)
    (live0 : (caller.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (cache0 : (caller.locals[0]'(by omega)).layout = none)
    (live7 : (caller.locals[7]'(by omega)).value = .live (.immediate .uninit))
    (live8 : (caller.locals[8]'(by omega)).value = .live (.immediate .uninit))
    (cache8 : (caller.locals[8]'(by omega)).layout = none)
    (live9 : (caller.locals[9]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (caller.locals[9]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (live10 : (caller.locals[10]'(by omega)).value = .live (.immediate .uninit))
    (cache10 : (caller.locals[10]'(by omega)).layout = none)
    (live13 : (caller.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (cache13 : (caller.locals[13]'(by omega)).layout = none) :
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = caller.body ∧ result.bodyIdentity = caller.bodyIdentity ∧ result.functionInstance = caller.functionInstance ∧
      result.extra = caller.extra ∧ result.returnPlace = caller.returnPlace ∧ result.returnContinuation = caller.returnContinuation ∧
      result.vaList = caller.vaList ∧ result.localsIdentity = caller.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = beforeMachine.memory ∧
      finalMachine.borrowTracker = some (PositiveLenPost.trackerAfter tracker fresh id) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  obtain ⟨lenMachine,lenTrace,memoryEq,trackedEq,fg,fv,fr,ff,fu,fnc,fa,ft,fb,fe,threadExists⟩ := S03NonliveLenCall.returns_zero
    options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id metadataTag base offset nonzero caller beforeMachine tracker enabled defaultMode nextTag nonliveMetadata absent cachedAddress fresh valid live uncached
    noClocks ghost shallow race thread active cachedThread metadata notConstructed sourceBody identity callee located
    source sourceValid sourceLive sourceCached backend unchecked noGc fixed
  have rejected : count > (0 : UInt64)/2 := by simpa using (UInt64.pos_iff_ne_zero.mpr countNonzero)
  obtain ⟨result,tailTrace,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,rAll⟩ := GeneralBorrowRawLenRejectedFrame.executes
    options limits remaining span source debugOff validityFuel validationEq caller lenMachine 0 count rejected frameSize
    (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    sourceLive live13 cache13 live0 cache0 live7 live8 cache8 live9 cache9 live10 cache10
    sourceBody identity callee allImmediate noClocks (PositiveLenPost.trackerAfter tracker fresh id) trackedEq
    defaultMode fg fv fu fnc ff
  let finalMachine := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span lenMachine))
  have ledger := GeneralBorrowRawLenRejectedFrame.machine_ledger options remaining span lenMachine
  have flags := RootZeroCompleteState.tick_flags options remaining span
    (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span lenMachine))
  have flags1 := RootZeroCompleteState.tick_flags options remaining span (RootZeroCompleteState.tick options remaining span lenMachine)
  have flags0 := RootZeroCompleteState.tick_flags options remaining span lenMachine
  have finalGhost : finalMachine.user.payload.ghost = false := by
    simp only [finalMachine,RootZeroCompleteState.tick_ghost]
    exact fg
  have finalShallow : finalMachine.user.payload.validation = .Shallow := by
    simp only [finalMachine,RootZeroCompleteState.tick_shallow]
    exact fv
  refine ⟨result,finalMachine,SuccessfulTrace.append lenTrace tailTrace,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,rAll,
    ledger.1.trans memoryEq,ledger.2.1.trans trackedEq,finalGhost,finalShallow,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ledger.2.2.1.trans fr
  · rw [show finalMachine.threads = lenMachine.threads from ledger.2.2.2.1]
    exact ff
  · exact flags.1.trans (flags1.1.trans (flags0.1.trans fu))
  · exact flags.2.trans (flags1.2.trans (flags0.2.trans fnc))
  · exact ledger.2.2.2.2.1.trans fa
  · exact ledger.2.2.2.2.2.1.trans ft
  · exact ledger.2.2.2.2.2.2.2.trans fb
  · exact ledger.2.2.2.2.2.2.1.trans fe
  · rw [show finalMachine.threads = lenMachine.threads from ledger.2.2.2.1]
    exact threadExists

end
end DuplicatePrefix.S03NonliveLenToReturn
