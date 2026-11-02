import duplicate_prefix.GeneralBorrowFreshRootScopedAsMutCopyLedger
import duplicate_prefix.GeneralBorrowFreshRootScopedAsMutCompleteExactLedger
import duplicate_prefix.GenericAsMutCallFrontend
import duplicate_prefix.GenericCallStages
import duplicate_prefix.SourceControl
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutCallerExactLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext AsMutCallTerminator
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowFreshRootScopedFnEntry.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (headroom : entry.allocation.extra.nodes.size+1 < 65536)
    (source : PreparedContracts.SourceComparator) (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (threadTop : thread.topUserRelevantFrame = some 0)
    (size : caller.locals.size = 25)
    (callerBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (track : caller.trackCallerArg = none) (relevant : caller.extra.userRelevance > 0)
    (immediate : CopyHelperCleanup.AllImmediate caller)
    (located : caller.location = .mir ⟨6,8⟩)
    (valid16 : 16 < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ next : GeneralBorrowFreshRootScopedAsMutToCopy.Input, ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller machine)
        (Storage.withCurrent #[] result finalMachine) ∧
      next.caller = AsMutUncachedCall.cachedCaller caller destValid ∧ next.tag = tracker.global.nextPointerTag ∧ next.count = count ∧
      PositiveRootSuccessProfile.FrameShape (AsMutUncachedCall.cachedCaller caller destValid) result (GeneralBorrowFreshRootScopedAsMutToCopy.pointer next)
        (Scalar.fromPointer cfg.access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset+count)))) count ∧
      finalMachine.memory = GeneralBorrowFreshRootScopedAsMutToCopy.memory next ∧
      finalMachine.borrowTracker = some (GeneralBorrowFreshRootScopedAsMutToCopy.held next) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts
        (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree
        (GeneralBorrowFreshRootScopedAsMutToCopy.held next).global ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive
        (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree
        (GeneralBorrowFreshRootScopedAsMutToCopy.held next).global.protectedTags
        next.anchor next.selected next.maximum next.offset next.len) ∧
      (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree.indexOfTag next.tag = some next.anchor ∧
      GeneralBorrowFreshRootScopedAsMutCopyLedger.Metadata entry machine id base offset len count next ∧
      GeneralBorrowFreshRootScopedAsMutCopyLedger.Outcome next finalMachine ∧
      GeneralBorrowFreshRootScopedAsMutCopyLedger.Resources
        (GeneralBorrowFreshRootScopedFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len)
        (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)
        tracker.global.nextPointerTag next ∧
      GeneralBorrowFreshRootScopedAsMutCopyLedger.Configuration options limits remaining span validityFuel next ∧
      next.machine.memory = RetagEntry.updatedMemory machine.memory id entry next.entry.allocation.extra ∧
      next.machine.user.addresses = machine.user.addresses := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] caller machine
  let root := AsMutUncachedCall.cachedCaller caller destValid
  let nextMachine := AsMutPtrReturn.accountedMachine options remaining span machine
  let accounted := Storage.withCurrent #[] caller nextMachine
  let destination := (LocalPlaces.localRuntimePlace 0 root 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  have carried : nextMachine.user.addresses = machine.user.addresses ∧
      nextMachine.user.payload.ghost = machine.user.payload.ghost ∧
      nextMachine.user.payload.validation = machine.user.payload.validation ∧
      nextMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      nextMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend := by
    unfold nextMachine AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have control : cfg.terminators.getControl nextMachine.user = TerminatorClock.advance (cfg.terminators.getControl machine.user) := by
    unfold nextMachine AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have rootSize : root.locals.size = caller.locals.size := by simp only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  have rootValid : 15 < root.locals.size := by rw [rootSize];exact destValid
  have rootLive : root.locals[15].value = .live (.immediate .uninit) := by
    simpa [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using destLive
  have rootCached : root.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
  have other (index : Nat) (different : index ≠ 15) : root.locals[index]? = caller.locals[index]? := by
    simp only [root,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different,↓reduceIte]
  have original16 : caller.locals[16]?.map (·.value) = some (.live (.immediate value)) := by
    rw [Array.getElem?_eq_getElem valid16];exact congrArg some value16
  have nextMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] root nextMachine)).metadata = PreparedReflection.actual.runtime := by
    change nextMachine.user.payload.payload.user.types.metadata = _
    rw [carried.2.2.2.1];exact metadata
  have nextNotConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] root nextMachine)).entries.any (·.value.ty == 4) = false := by
    change nextMachine.user.payload.payload.user.types.entries.any _ = _
    rw [carried.2.2.2.1];exact notConstructed
  obtain ⟨packet,result,finalMachine,entered,trace,callerEq,tagEq,countEq,shape,memory,tracked,postRuntime,postPositive,tagged,packetMetadata,outcome,resources,configuration,packetMemory,packetAddresses⟩ :=
    GeneralBorrowFreshRootScopedAsMutCompleteExactLedger.complete options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds root nextMachine tracker enabled defaultMode fresh runtime
      raw rawTag rawOffset rawLen capacity rootValid rootLive rootCached callerClocks
      (carried.2.1.trans ghost) (carried.2.2.1.trans shallow)
      (by rw [carried.1];exact cachedAddress) present race nextMetadata nextNotConstructed thread index current active top topPresent
      headroom source budget dispatch (carried.2.2.2.2.trans backend)
      (by rw [control];exact unchecked) (by rw [control];exact noGc) fixed threadTop
      (rootSize.trans size) callerBody identity callee track relevant
      (CopyHelperCleanup.all_immediate_cache caller 15 CopyCompilerFacts.destPointerLayout destValid immediate)
      value (by rw [other 16 (by decide)];exact original16) count countPositive within
      (by rw [other 2 (by decide)];exact slot2) (by rw [other 13 (by decide)];exact slot13)
      (by intro slot lower upper;rw [other slot (by omega)];exact unused slot lower upper)
  have effect := GenericAsMutCallFrontend.call_uncached options limits remaining budget dispatch span debugOff source cmp
    caller _ nextMachine _ value callerBody identity callee located valid16 value16 cached16 destValid .uninit destLive uncached callerClocks
    (carried.2.1.trans ghost) (carried.2.2.2.2.trans backend) race entered
  have accounting := SourceControl.before_terminator cfg limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () initial = (accounted,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[6]? = some block := by rw [callerBody];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  have callStep := GenericCallStages.source_step cfg limits () initial accounted _ caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue sourceKind fnSpan
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement source_call accounting' effect
    (by simp [Storage.withCurrent,accounted])
  have extras : nextMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold nextMachine AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have nextMemory : nextMachine.memory = machine.memory := by
    unfold nextMachine AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  have packetMemory' : packet.machine.memory = RetagEntry.updatedMemory machine.memory id entry packet.entry.allocation.extra := by rw [packetMemory,nextMemory]
  exact ⟨packet,result,finalMachine,SuccessfulTrace.Trace.next callStep trace,callerEq,tagEq,countEq,shape,memory,tracked,postRuntime,postPositive,tagged,
    ⟨packetMetadata.idEq,packetMetadata.baseEq,packetMetadata.offsetEq,packetMetadata.lenEq,packetMetadata.countEq,packetMetadata.entry,packetMetadata.extras.trans extras⟩,outcome,resources,configuration,packetMemory',packetAddresses.trans carried.1⟩
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutCallerExactLedger
