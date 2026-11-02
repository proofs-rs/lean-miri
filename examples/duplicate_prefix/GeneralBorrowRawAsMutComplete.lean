import duplicate_prefix.GeneralBorrowRawAsMutBodyShape
import duplicate_prefix.GeneralBorrowRawAsMutToCopy
import duplicate_prefix.GeneralBorrowRawFnEntryOrder
namespace DuplicatePrefix.GeneralBorrowRawAsMutComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem complete
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
    (raw : GeneralBorrowRawFnEntry.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (destCached : caller.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] caller machine)
      (LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent #[] caller machine)
      (LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
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
    (temp16 : Immediate Provenance)
    (live16 : caller.locals[16]?.map (·.value) = some (.live (.immediate temp16)))
    (count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let before := Storage.withCurrent #[] caller machine
    let destination := (LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := GeneralBorrowRawAsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ next : GeneralBorrowRawAsMutToCopy.Input, ∃ result finalMachine,
      Call.initStackFrame (ExecutionMachine.callHooks cfg limits) ()
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
        .ok () (Storage.withCurrent #[caller] frame resultMachine) ∧
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[caller] frame resultMachine)
        (Storage.withCurrent #[] result finalMachine) ∧
      next.caller = caller ∧ next.tag = tracker.global.nextPointerTag ∧ next.count = count ∧
      PositiveRootSuccessProfile.FrameShape caller result (GeneralBorrowRawAsMutToCopy.pointer next)
        (Scalar.fromPointer cfg.access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset+count)))) count ∧
      finalMachine.memory = GeneralBorrowRawAsMutToCopy.memory next ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held next) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts
        (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held next).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive
        (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held next).global.protectedTags
        (some next.anchor) (some next.selected) next.maximum next.offset next.len) ∧
      (next.entry.allocation.extra.releaseProtector next.tag next.tracker.global.protectedTags).tree.indexOfTag next.tag = some next.anchor := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent #[] caller machine
  let destination := (LocalPlaces.localRuntimePlace 0 caller 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
  let frame := GeneralBorrowRawAsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  obtain ⟨done,entered,trace,located,pointerDone,bodyDone,sizeDone,one,two,three,four,varargs,direct,extra,returnPlace,continuation,
    afterRuntime,child,lookup,⟨childPositive⟩,activity⟩ :=
    GeneralBorrowRawAsMutBodyShape.before_return options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds #[] caller machine tracker enabled defaultMode fresh runtime
      raw rawTag rawOffset rawLen capacity 15 destValid .uninit destLive destCached callerClocks ghost shallow cachedAddress present race
      metadata notConstructed thread index current active top topPresent
  have fields : resultMachine.user.addresses = machine.user.addresses ∧
      resultMachine.user.payload.ghost = machine.user.payload.ghost ∧
      resultMachine.user.payload.validation = machine.user.payload.validation ∧
      resultMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      resultMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      resultMachine.dataRace = machine.dataRace ∧
      resultMachine.threads.fixedScheduling = machine.threads.fixedScheduling := by
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,postMachine,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have registeredPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced postMachine.memory id resultEntry
  have control : cfg.terminators.getControl resultMachine.user = cfg.terminators.getControl machine.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,postMachine,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> rfl
  have activeAfter : resultMachine.threads.activeThread? = some (PushThread.after thread 1 (AsMutFrame.rank options.userRelevantCrates) current.extra.userRelevance) := by
    change (GenericPushRelevance.afterPush (AsMutPush.fresh machine).1 1 (AsMutFrame.rank options.userRelevantCrates) current.extra.userRelevance).threads.activeThread? = _
    exact PushThread.active_after _ thread 1 _ _ active
  have resources := GeneralBorrowRawFnEntryResources.resources entry.allocation.extra tracker {} id runtime raw
  have metadataHidden := GeneralBorrowRawFnEntryHidden.hidden entry.allocation.extra tracker {} id runtime raw
  have limitsOrder := GeneralBorrowRawFnEntryOrder.conditional entry.allocation.extra tracker {} id runtime raw headroom
  simp only [rawTag,rawOffset,rawLen] at resources metadataHidden limitsOrder
  obtain ⟨_,_,_,roots,_,_,_,rest⟩ := resources
  obtain ⟨hiddenChild,node,hiddenLookup,nodePresent,sameTag,hidden⟩ := metadataHidden
  have childEqual : hiddenChild = child := Option.some.inj (hiddenLookup.symm.trans lookup)
  subst hiddenChild
  have doneValid : 0 < done.locals.size := by omega
  have doneSlot : done.locals[0] = ⟨.live (.immediate (.scalar (Scalar.fromPointer cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem doneValid).symm.trans pointerDone)
  have frameFacts := GeneralBorrowRawAsMutShape.fixed options before destination value adjusted id tracker.global.nextPointerTag
  have frameRace : frame.extra.dataRace = none := by
    change ((AsMutPush.fresh before.machine).1.dataRace.map _) = none
    change machine.dataRace.map _ = none
    rw [race];rfl
  let next : GeneralBorrowRawAsMutToCopy.Input := {
    options := options, limits := limits, remaining := remaining, span := span, debug := debugOff,
    fuel := validityFuel, validation := validationEq, dynamicFuel := dynamicFuel, dynamic := fuelEq, cmp := cmp,
    source := source,budget := budget,dispatch := dispatch,caller := caller,machine := resultMachine,id := id,
    tag := tracker.global.nextPointerTag,entry := resultEntry,base := base,offset := offset,len := len,
    positive := positive,nonzero := nonzero,signedFits := signedFits,bounds := bounds,
    cachedAddress := by rw [fields.1];exact cachedAddress,
    present := registeredPresent,tracker := held,tracked := rfl,mode := defaultMode,
    runtime := afterRuntime,anchor := child,selected := raw.selected,maximum := raw.maximum,owner := childPositive,
    node := node,nodePresent := nodePresent,sameTag := sameTag,hidden := hidden,tagged := lookup,
    distinct := by change finalTree.roots.toList.Nodup;rw [roots];exact raw.distinct,
    order := limitsOrder.1,short := limitsOrder.2,activity := activity,
    helperFrame := done,helperBody := bodyDone,helperLocation := located,helperValid0 := doneValid,
    helperLive0 := by rw [doneSlot],helperCached0 := by rw [doneSlot],
    helperClocks := by rw [extra];exact frameRace,
    helperDestination := by change done.returnPlace.toRuntimePlace = _;rw [returnPlace];change frame.returnPlace.toRuntimePlace = _;rw [frameFacts.2.2.2.2.1];rfl,
    helperContinuation := continuation.trans frameFacts.2.2.2.2.2.1,
    helperDirect := direct,helperVarargs := varargs,
    helperTracked := by rw [extra];exact frameFacts.2.2.2.2.2.2.2,
    ghost := fields.2.1.trans ghost,shallow := fields.2.2.1.trans shallow,race := fields.2.2.2.2.2.1.trans race,
    backend := fields.2.2.2.2.1.trans backend,
    valid15 := destValid,live15 := destLive,cached15 := destCached,clocks := callerClocks,
    metadata := by change resultMachine.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2.1];exact metadata,
    notConstructed := by change resultMachine.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2.1];exact notConstructed,
    thread := thread,newRank := AsMutFrame.rank options.userRelevantCrates,oldRank := current.extra.userRelevance,
    active := activeAfter,top := threadTop,unchecked := by rw [control];exact unchecked,noGc := by rw [control];exact noGc,
    fixed := fields.2.2.2.2.2.2.trans fixed,size := size,body := callerBody,identity := identity,callee := callee,
    track := track,relevant := relevant,immediate := immediate,temp16 := temp16,live16 := live16,count := count,
    countPositive := countPositive,within := within,slot2 := slot2,slot13 := slot13,unused := unused }
  obtain ⟨result,finalMachine,tail,shape,memory,tracked,_,_,_,_,_,_,_,_,_,_,_,afterRuntime,afterPositive,afterTagged⟩ := GeneralBorrowRawAsMutToCopy.run next
  exact ⟨next,result,finalMachine,entered,SuccessfulTrace.append trace tail,rfl,rfl,rfl,shape,memory,tracked,afterRuntime,afterPositive,afterTagged⟩
end
end DuplicatePrefix.GeneralBorrowRawAsMutComplete
