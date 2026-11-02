import duplicate_prefix.GeneralBorrowRawDefaultToTrueReturn
import duplicate_prefix.GeneralBorrowRawMutableParentRestore
import duplicate_prefix.GeneralBorrowRawDefaultExactLedger
import duplicate_prefix.GeneralBorrowRawMutableTargetActivity
import duplicate_prefix.RootSuccessToReturn
import duplicate_prefix.GeneralBorrowRawCopyTargetActivity
import duplicate_prefix.GeneralBorrowRawAsMutActualCopyIndependentFuel
namespace DuplicatePrefix.GeneralBorrowRawDefaultToTrueReturnIndependentFuel
open DuplicatePrefix.GeneralBorrowRawDefaultToTrueReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
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
    (raw : GeneralBorrowRawDefault.Input entry.allocation.extra tracker.global)
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
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (headroom : entry.allocation.extra.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
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
    (located : caller.location = .mir ⟨6,7⟩)
    (valid16 : 16 < caller.locals.size)
    (dead16 : caller.locals[16].value = .live (.immediate .uninit))
    (uncached16 : caller.locals[16].layout = none)
    (valid1 : 1 < caller.locals.size)
    (source1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached1 : caller.locals[1].layout = some ActualReferenceMetadata.reference)
    (count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩)
    (target : UniIndex)
    (oldActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len))
    (initial0 : caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (statementBudget : Nat) (statementFuel : limits.validation = statementBudget+1)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (maskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count)))
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (storageFits : entry.allocation.len+64 < 18446744073709551616)
    (mutable : entry.allocation.mutability = .Mut)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ packet : GeneralBorrowRawAsMutToCopy.Input, ∃ result done finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller machine)
        (Storage.withCurrent #[] done finalMachine) ∧
      ReadyFrame caller done ∧
      finalMachine.memory = CopyHelperCall.memoryAfter machine.memory id entry.kind result ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨entry.kind,result⟩) ∧
      result.byteSize = entry.allocation.byteSize ∧ result.len = entry.allocation.len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.extra (GeneralBorrowRawAsMutToCopy.held packet).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags
        (some raw.parent) (some packet.selected) packet.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.extra target .Write offset (offset+len) ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held packet) ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      finalMachine.user.payload.payload.user.backend = .none ∧ finalMachine.user.payload.ghost = false ∧
      finalMachine.user.payload.validation = .Shallow ∧ finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      (cfg.terminators.getControl finalMachine.user).gcInterval = 0 ∧
      ∃ activeThread, finalMachine.threads.activeThread? = some activeThread := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  have initialRuntime := runtime
  obtain ⟨packet,copyCaller,beforeCopy,prefixTrace,packetTag,packetCount,shape,memory,tracked,postRuntime,postPositive,postTagged,
    metadataLedger,outcome,secondFresh,resources,configuration,packetCaller,packetMemory,packetAddresses⟩ :=
    GeneralBorrowRawDefaultExactLedger.invoke options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh runtime raw rawTag rawOffset rawLen capacity destValid destLive uncached callerClocks ghost shallow cachedAddress present race metadata notConstructed thread active headroom tagsRoom preciseOff implicitOff source budget dispatch backend unchecked noGc fixed threadTop size callerBody identity callee track relevant immediate located valid16 dead16 uncached16 valid1 source1 cached1 count countPositive within slot2 slot13 unused
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write raw.offset (raw.offset+raw.len) := by
    rw [rawOffset,rawLen];exact oldActivity
  have literalActivity := GeneralBorrowRawMutableTargetActivity.suffix entry.allocation.extra tracker runtime raw headroom tagsRoom target initialActivity
  simp only [rawTag,rawOffset,rawLen] at literalActivity
  have oldActive : GeneralBorrowFreshActiveWithin.ActiveWithin
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
      target .Write offset (offset+len) := by
    rw [resources.treeEq,resources.tagEq,resources.trackerEq]
    exact literalActivity.2.2
  have shape' : PositiveRootSuccessProfile.FrameShape packet.caller copyCaller (GeneralBorrowRawAsMutToCopy.pointer packet)
      (Scalar.fromPointer (PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).access.runtime.base
        (Pointer.new (Provenance.concrete packet.id packet.tag) (Size.ofBytes (packet.base+packet.offset+packet.count)))) packet.count := by
    simpa only [configuration.optionsEq,configuration.remainingEq,configuration.spanEq,
      metadataLedger.idEq,metadataLedger.baseEq,metadataLedger.offsetEq,metadataLedger.countEq] using shape
  have packetStorage : packet.entry.allocation.len = packet.entry.allocation.byteSize.bytes.toNat := by
    rw [metadataLedger.entry];exact storage
  have packetMask : InitMaskCopy.WellFormed packet.entry.allocation.initializationMask := by rw [metadataLedger.entry];exact maskValid
  have packetMaskLen : packet.entry.allocation.initializationMask.len = packet.entry.allocation.byteSize := by rw [metadataLedger.entry];exact maskLen
  have packetInit : InitMaskCopy.InitializedOn packet.entry.allocation.initializationMask (Size.ofBytes packet.offset) (Size.ofBytes (packet.offset+packet.count)) := by
    rw [metadataLedger.entry,metadataLedger.offsetEq,metadataLedger.countEq];exact initialized
  have packetProvenance : ProvenanceCopy.WellFormed packet.entry.allocation.provenanceMap packet.entry.allocation.len := by rw [metadataLedger.entry];exact provenance
  have packetFits : packet.entry.allocation.len+64 < 18446744073709551616 := by rw [metadataLedger.entry];exact storageFits
  have packetMutable : packet.entry.allocation.mutability = .Mut := by rw [metadataLedger.entry];exact mutable
  have packetExtras : packet.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == packet.id) = some (packet.id,⟨none,#[]⟩) := by
    rw [metadataLedger.extras,metadataLedger.idEq];exact extras
  have packetBounded : packet.count ≤ (PreparedContracts.actualConfig packet.options () (packet.remaining+1) packet.span).projection.maxSizeOfVal.bytes := by
    rw [metadataLedger.countEq,configuration.optionsEq,configuration.remainingEq,configuration.spanEq];exact bounded
  have packetFuel : packet.limits.validation = statementBudget+1 := by rw [configuration.limitsEq];exact statementFuel
  obtain ⟨result,finalMachine,trace,live,bytes,length,tree,snapshot,copyRuntime,positive,trackerAfter,memoryAfter,addresses,types,
    extrasAfter,backendAfter,ghostAfter,shallowAfter,raceAfter,fixedAfter,uncheckedAfter,noGcAfter,activeAfter⟩ :=
    GeneralBorrowRawAsMutActualCopyIndependentFuel.from_suffix packet copyCaller beforeCopy shape' memory tracked outcome statementBudget packetFuel
      packetStorage packetMask packetMaskLen packetInit packetProvenance packetFits packetMutable packetExtras packetBounded
  obtain ⟨copyInput,_,_,_⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have oldActive' : GeneralBorrowFreshActiveWithin.ActiveWithin
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
      target .Write packet.offset (packet.offset+packet.len) := by
    rw [metadataLedger.offsetEq,metadataLedger.lenEq];exact oldActive
  have afterActive := (GeneralBorrowRawCopyTargetActivity.accesses _ _ packet.tag packet.offset packet.len packet.count copyInput target oldActive').2
  rw [←tree] at afterActive
  have postNodes : result.extra.nodes = packet.entry.allocation.extra.nodes := by
    rw [tree]
    exact GeneralBorrowRawMutableParentRestore.copy_nodes packet
  have resourcesRaw : GeneralBorrowRawAsMutCopyLedger.Resources
      (GeneralBorrowRawFnEntryArgument.finalTree
        (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags raw.parentTag tracker.global.nextPointerTag raw.offset raw.len .VisitChildrenOfAccessed).tree
        (ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom) tracker.global.nextPointerTag raw.offset raw.len)
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom) secondFresh)
        (ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom).global.nextPointerTag)
      (ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom).global.nextPointerTag packet := by
    simpa only [rawTag,rawOffset,rawLen] using resources
  obtain ⟨currentPositive⟩ := positive
  have restored := GeneralBorrowRawMutableParentRestore.restore entry.allocation.extra tracker id runtime raw headroom tagsRoom
    packet secondFresh resourcesRaw metadataLedger.idEq result.extra postNodes copyRuntime currentPositive
  have originalPositive : Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags
      (some raw.parent) (some packet.selected) packet.maximum offset len) := by
    simpa only [metadataLedger.offsetEq,metadataLedger.lenEq] using restored
  have oldActiveAfter : GeneralBorrowFreshActiveWithin.ActiveWithin result.extra target .Write offset (offset+len) := by
    simpa only [metadataLedger.offsetEq,metadataLedger.lenEq] using afterActive
  have finalLive : finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨entry.kind,result⟩) := by
    have kindEq := congrArg LocalAllocation.kind metadataLedger.entry
    rw [metadataLedger.idEq,kindEq] at live
    exact live
  have bytesEq : result.byteSize = entry.allocation.byteSize := by rw [metadataLedger.entry] at bytes;exact bytes
  have lengthEq : result.len = entry.allocation.len := by rw [metadataLedger.entry] at length;exact length
  have trace' : SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] copyCaller beforeCopy)
      (Storage.withCurrent #[] (CopyRootOutput.caller copyCaller (by rw [shape.size];decide)) finalMachine) := by
    simpa only [configuration.optionsEq,configuration.limitsEq,configuration.remainingEq,configuration.spanEq] using trace
  let rootFrame := CopyRootOutput.caller copyCaller (by rw [shape.size];decide)
  have rootSize : rootFrame.locals.size = 25 := (CopyRootOutput.metadata copyCaller (by rw [shape.size];decide)).2.2.2.2.2.2.2.2.2.1.trans shape.size
  have rv (slot : Fin 25) : slot.val < rootFrame.locals.size := by rw [rootSize];exact slot.isLt
  have packet0 : packet.caller.locals[0]? = caller.locals[0]? := by
    rw [packetCaller]
    simp only [AsMutUncachedCall.cachedCaller,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set]
    rfl
  have rootOther (slot : Nat) (different : slot ≠ 18) : rootFrame.locals[slot]? = copyCaller.locals[slot]? :=
    CopyRootOutput.other copyCaller _ slot different
  have root0 : rootFrame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ :=
    (rootOther 0 (by decide)).trans (shape.slot0.trans (packet0.trans initial0))
  have root15 := (rootOther 15 (by decide)).trans shape.slot15
  have root17 := (rootOther 17 (by decide)).trans shape.slot17
  have root19 := (rootOther 19 (by decide)).trans shape.slot19
  have root21 := (rootOther 21 (by decide)).trans shape.slot21
  have root24 := (rootOther 24 (by decide)).trans shape.slot24
  have row (slot : Fin 25) (value : LocalState Provenance LocalLayout) (known : rootFrame.locals[slot.val]? = some value) :
      rootFrame.locals[slot.val]'(rv slot) = value := Option.some.inj ((Array.getElem?_eq_getElem (rv slot)).symm.trans known)
  have root18 := CopyRootOutput.slot18 copyCaller (by rw [shape.size];decide)
  have rootRace : rootFrame.extra.dataRace = none := by change copyCaller.extra.dataRace = none;rw [shape.extra];exact packet.clocks
  have uncheckedCopy : (cfg.terminators.getControl finalMachine.user).checkedArithmetic = false := by simpa only [configuration.optionsEq,configuration.remainingEq,configuration.spanEq] using uncheckedAfter
  have noGcCopy : (cfg.terminators.getControl finalMachine.user).gcInterval = 0 := by simpa only [configuration.optionsEq,configuration.remainingEq,configuration.spanEq] using noGcAfter
  obtain ⟨done,cleanup,doneShape⟩ := RootSuccessToReturn.reaches_return options limits remaining span source debugOff validityFuel validationEq #[] rootFrame finalMachine rootSize
    (.scalar (GeneralBorrowRawAsMutToCopy.pointer packet)) .uninit (.scalar (GeneralBorrowRawAsMutToCopy.pointer packet))
    (.scalar (Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id packet.tag) (Size.ofBytes (base+offset+count)))))
    (.scalar (.fromScalarInt (.ofUInt64 count)))
    (by rw [row ⟨0,by decide⟩ _ root0]) (by rw [row ⟨0,by decide⟩ _ root0])
    (by rw [row ⟨15,by decide⟩ _ root15]) (by rw [row ⟨17,by decide⟩ _ root17]) (by rw [row ⟨17,by decide⟩ _ root17])
    (by rw [root18]) (by rw [row ⟨19,by decide⟩ _ root19]) (by rw [row ⟨21,by decide⟩ _ root21]) (by rw [row ⟨24,by decide⟩ _ root24])
    (shape.body.trans packet.body) (shape.identity.trans packet.identity) (shape.callee.trans packet.callee) rfl rootRace
    (GeneralBorrowRawAsMutToCopy.held packet) trackerAfter packet.mode ghostAfter shallowAfter uncheckedCopy noGcCopy fixedAfter
  let ready := {done with location := .mir ⟨10,0⟩}
  let readyMachine := (SourceControl.accounted cfg.terminators (Storage.withCurrent #[] done finalMachine)).machine
  have frameReady : ReadyFrame caller ready := by
    constructor
    · rw [show ready.body = done.body from rfl,doneShape.body];change copyCaller.body = caller.body;rw [shape.body,packetCaller];rfl
    · rw [show ready.bodyIdentity = done.bodyIdentity from rfl,doneShape.identity];change copyCaller.bodyIdentity = caller.bodyIdentity;rw [shape.identity,packetCaller];rfl
    · rw [show ready.functionInstance = done.functionInstance from rfl,doneShape.callee];change copyCaller.functionInstance = caller.functionInstance;rw [shape.callee,packetCaller];rfl
    · rw [show ready.extra = done.extra from rfl,doneShape.extra];change copyCaller.extra = caller.extra;rw [shape.extra,packetCaller];rfl
    · rw [show ready.returnPlace = done.returnPlace from rfl,doneShape.destination];change copyCaller.returnPlace = caller.returnPlace;rw [shape.destination,packetCaller];rfl
    · rw [show ready.returnContinuation = done.returnContinuation from rfl,doneShape.continuation];change copyCaller.returnContinuation = caller.returnContinuation;rw [shape.continuation,packetCaller];rfl
    · rw [show ready.vaList = done.vaList from rfl,doneShape.varargs];change copyCaller.vaList = caller.vaList;rw [shape.varargs,packetCaller];rfl
    · rw [show ready.localsIdentity = done.localsIdentity from rfl,doneShape.localsIdentity];change copyCaller.localsIdentity = caller.localsIdentity;rw [shape.localsIdentity,packetCaller];rfl
    · rw [show ready.trackCallerArg = done.trackCallerArg from rfl,doneShape.trackedCaller];change copyCaller.trackCallerArg = caller.trackCallerArg;rw [shape.trackedCaller,packetCaller];rfl
    · exact doneShape.size
    · rfl
    · exact doneShape.output
    · exact doneShape.immediate (CopyRootOutput.all_immediate copyCaller _ shape.immediate)
  have beforeCopyMemory : beforeCopy.memory = RetagEntry.updatedMemory machine.memory id entry
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree := by
    rw [memory]
    unfold GeneralBorrowRawAsMutToCopy.memory
    change RetagEntry.updatedMemory packet.machine.memory packet.id packet.entry _ = _
    rw [metadataLedger.idEq,packetMemory,metadataLedger.entry]
    exact RetagEntry.updated_memory_twice machine.memory id entry packet.entry.allocation.extra _
  have finalMemory : finalMachine.memory = CopyHelperCall.memoryAfter machine.memory id entry.kind result := by
    rw [memoryAfter,beforeCopyMemory,metadataLedger.idEq]
    have kindEq := congrArg LocalAllocation.kind metadataLedger.entry
    rw [kindEq]
    exact MemoryCopyBridge.live_update_twice machine.memory id
      {entry with allocation := entry.allocation.setExtra _} ⟨entry.kind,result⟩
  have readyFields : readyMachine.memory = finalMachine.memory ∧ readyMachine.borrowTracker = finalMachine.borrowTracker ∧
      readyMachine.user.addresses = finalMachine.user.addresses ∧ readyMachine.user.payload.payload.user.runtime.extras = finalMachine.user.payload.payload.user.runtime.extras ∧
      readyMachine.user.payload.payload.user.backend = finalMachine.user.payload.payload.user.backend ∧ readyMachine.user.payload.ghost = finalMachine.user.payload.ghost ∧
      readyMachine.user.payload.validation = finalMachine.user.payload.validation ∧ readyMachine.dataRace = finalMachine.dataRace ∧ readyMachine.threads = finalMachine.threads := by
    unfold readyMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have readyControl : cfg.terminators.getControl readyMachine.user = TerminatorClock.advance (cfg.terminators.getControl finalMachine.user) := by
    unfold readyMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  refine ⟨packet,result,ready,readyMachine,SuccessfulTrace.append (SuccessfulTrace.append prefixTrace trace') cleanup,frameReady,
    readyFields.1.trans finalMemory,?_,bytesEq,lengthEq,copyRuntime,originalPositive,oldActiveAfter,readyFields.2.1.trans trackerAfter,
    ?_,?_,readyFields.2.2.2.2.1.trans backendAfter,readyFields.2.2.2.2.2.1.trans ghostAfter,readyFields.2.2.2.2.2.2.1.trans shallowAfter,
    readyFields.2.2.2.2.2.2.2.1.trans raceAfter,?_,?_,?_,?_⟩
  · rw [readyFields.1];exact finalLive
  · rw [readyFields.2.2.1,addresses,outcome.addresses,packetAddresses]
  · rw [readyFields.2.2.2.1,extrasAfter,outcome.extras,metadataLedger.extras]
  · change readyMachine.threads.fixedScheduling = true
    rw [readyFields.2.2.2.2.2.2.2.2]
    exact fixedAfter
  · rw [readyControl];exact uncheckedCopy
  · rw [readyControl];exact noGcCopy
  · change ∃ thread, readyMachine.threads.activeThread? = some thread
    rw [readyFields.2.2.2.2.2.2.2.2]
    exact activeAfter
end
end DuplicatePrefix.GeneralBorrowRawDefaultToTrueReturnIndependentFuel

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GeneralBorrowRawDefaultToTrueReturnIndependentFuel.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "independent-fuel copy return depends on unapproved axiom {dependency}"
