import duplicate_prefix.WildcardOrderedMissLenCallReturn
import duplicate_prefix.EmptyRootLenCall
import duplicate_prefix.LenCallReturn
namespace DuplicatePrefix.WildcardOrderedMissRootLenCall
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend LenCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem returns_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (caller : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : beforeMachine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
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
    (addressMode : beforeMachine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardOrderedMissAddress.Miss beforeMachine.user.addresses address)
    (metadata : beforeMachine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : beforeMachine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : beforeMachine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[] (resultFrame caller valid 0) finalMachine) ∧
      finalMachine.memory = beforeMachine.memory ∧
      finalMachine.borrowTracker = some (ReferenceBorrowDriver.allocatedTracker tracker fresh) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = beforeMachine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      ∃ finalThread, finalMachine.threads.activeThread? = some finalThread := by
  let next := PtrMetadataReturn.accountedMachine options remaining span beforeMachine
  let root := cachedCaller caller valid
  have nextTracked : next.borrowTracker = some tracker := enabled
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation];exact shallow
  have nextActive : next.threads.activeThread? = some thread := active
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddresses : next.user.addresses=beforeMachine.user.addresses := by
    unfold next PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have nextMode : next.user.addresses.provenanceMode ≠ .strict := by rw [nextAddresses];exact addressMode
  have nextBelow : WildcardOrderedMissAddress.Miss next.user.addresses address := by rw [nextAddresses];exact miss
  let state := Storage.withCurrent #[] root next
  let destination := (LocalPlaces.localRuntimePlace 0 root 11 RootCompilerFacts.usizeLayout).stackView
  have topKnown : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some 0 := by
    simp only [FrameRelevance.top,cachedThread,Option.orElse_some]
  have presentKnown : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some root := by
    simp [state,LenPush.pushed,Storage.withCurrent]
  have typeEq : (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types =
      beforeMachine.user.payload.payload.user.types := by
    exact LenPushFacts.types_eq options remaining span #[] root beforeMachine root
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination root)).metadata = PreparedReflection.actual.runtime := by
    change (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types.metadata = _
    rw [typeEq]
    exact metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination root)).entries.any (·.value.ty == 4) = false := by
    change (LenPush.completed options.userRelevantCrates state destination root).machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false
    rw [typeEq]
    exact notConstructed
  exact WildcardOrderedMissLenCallReturn.integer_zero options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq address nonzero #[] caller next tracker nextTracked defaultMode fresh valid live uncached noClocks nextGhost nextShallow race thread 0 root nextActive topKnown presentKnown nextMode nextBelow postMetadata postNotConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached nextBackend beforeMachine rfl unchecked noGc fixed
end
end DuplicatePrefix.WildcardOrderedMissRootLenCall
