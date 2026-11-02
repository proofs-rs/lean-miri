import duplicate_prefix.GeneralBorrowRawReturnedBytes
import duplicate_prefix.GeneralBorrowRawMutableParentRestore
import duplicate_prefix.GeneralBorrowRawDefaultExitLedger
import duplicate_prefix.GeneralBorrowRawMutableRootMetadata
import duplicate_prefix.GeneralBorrowRawTrueReturnData
import duplicate_prefix.GeneralBorrowRawMutableTargetActivity
import duplicate_prefix.RootSuccessToReturn
import duplicate_prefix.GeneralBorrowRawCopyTargetActivity
import duplicate_prefix.GeneralBorrowRawAsMutActualCopy
namespace DuplicatePrefix.GeneralBorrowRawDefaultFullTrueObserved
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Exact ROOT frame identity at true Return; all fields follow from actual statements. -/
structure ReadyFrame (before after : CompilerFrameContext.ActualFrame) : Prop where
  body : after.body = before.body
  identity : after.bodyIdentity = before.bodyIdentity
  callee : after.functionInstance = before.functionInstance
  extra : after.extra = before.extra
  destination : after.returnPlace = before.returnPlace
  continuation : after.returnContinuation = before.returnContinuation
  varargs : after.vaList = before.vaList
  localsIdentity : after.localsIdentity = before.localsIdentity
  track : after.trackCallerArg = before.trackCallerArg
  size : after.locals.size = 25
  location : after.location = .mir ⟨10,0⟩
  output : after.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩
  immediate : CopyHelperCleanup.AllImmediate after
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
    (oldActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra raw.parent .Write offset (offset+len))
    (initial0 : caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩)
    (statementFuel : limits.validation = validityFuel+1)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (maskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+count)))
    (provenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (storageFits : entry.allocation.len+64 < 18446744073709551616)
    (mutable : entry.allocation.mutability = .Mut)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (bounded : count ≤ (PreparedContracts.actualConfig options () (remaining+1) span).projection.maxSizeOfVal.bytes)
    (ret : GeneralBorrowRawTrueReturnData.Data options remaining span caller machine tracker id entry parentTag raw.parent) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
    ∃ physical : GeneralBorrowRawRootBoolReturn.Input,
      physical.value = true ∧ physical.release.slotId = ret.slotId ∧ GeneralBorrowRawRootBoolReturn.Result physical ∧
      ∃ updated,
        SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller machine)
          (CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated) ∧
        ExecutionMachine.step cfg limits ()
          (CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated) =
          (CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated,.ok false) ∧
        CallSafety.NoUBBeforeReturn safety 1 (Storage.withCurrent #[] caller machine) ∧
        GeneralBorrowRawReturnedBytes.Encoded physical.context updated true := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  have initialRuntime := runtime
  obtain ⟨packet,copyCaller,beforeCopy,prefixTrace,packetTag,packetCount,shape,memory,tracked,postRuntime,postPositive,postTagged,
    metadataLedger,outcome,secondFresh,resources,configuration,packetCaller,packetMemory,packetAddresses,packetSelected,packetMaximum⟩ :=
    GeneralBorrowRawDefaultExitLedger.invoke options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh runtime raw rawTag rawOffset rawLen capacity destValid destLive uncached callerClocks ghost shallow cachedAddress present race metadata notConstructed thread active headroom tagsRoom preciseOff implicitOff source budget dispatch backend unchecked noGc fixed threadTop size callerBody identity callee track relevant immediate located valid16 dead16 uncached16 valid1 source1 cached1 count countPositive within slot2 slot13 unused
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra raw.parent .Write raw.offset (raw.offset+raw.len) := by
    rw [rawOffset,rawLen];exact oldActivity
  have literalActivity := GeneralBorrowRawMutableTargetActivity.suffix entry.allocation.extra tracker runtime raw headroom tagsRoom raw.parent initialActivity
  simp only [rawTag,rawOffset,rawLen] at literalActivity
  have oldActive : GeneralBorrowFreshActiveWithin.ActiveWithin
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
      raw.parent .Write offset (offset+len) := by
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
  have packetFuel : packet.limits.validation = packet.fuel+1 := by rw [configuration.limitsEq,configuration.fuelEq];exact statementFuel
  obtain ⟨result,finalMachine,trace,live,bytes,length,tree,snapshot,copyRuntime,positive,trackerAfter,memoryAfter,addresses,types,
    extrasAfter,backendAfter,ghostAfter,shallowAfter,raceAfter,fixedAfter,uncheckedAfter,noGcAfter,activeAfter⟩ :=
    GeneralBorrowRawAsMutActualCopy.from_suffix packet copyCaller beforeCopy shape' memory tracked outcome packetFuel
      packetStorage packetMask packetMaskLen packetInit packetProvenance packetFits packetMutable packetExtras packetBounded
  obtain ⟨copyInput,_,_,_⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have oldActive' : GeneralBorrowFreshActiveWithin.ActiveWithin
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
      raw.parent .Write packet.offset (packet.offset+packet.len) := by
    rw [metadataLedger.offsetEq,metadataLedger.lenEq];exact oldActive
  have afterActive := (GeneralBorrowRawCopyTargetActivity.accesses _ _ packet.tag packet.offset packet.len packet.count copyInput raw.parent oldActive').2
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
  have oldActiveAfter : GeneralBorrowFreshActiveWithin.ActiveWithin result.extra raw.parent .Write offset (offset+len) := by
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
  have postRoots : result.extra.roots = packet.entry.allocation.extra.roots := by
    rw [tree]
    exact GeneralBorrowRawMutablePolicyMetadata.copy_roots packet
  have rootMetadata := GeneralBorrowRawMutableRootMetadata.current entry.allocation.extra tracker id runtime raw headroom tagsRoom
    ret.sourceNode ret.sourcePresent ret.sourceHidden packet secondFresh resourcesRaw metadataLedger.idEq packetSelected result.extra postNodes postRoots
  obtain ⟨⟨currentNode,currentPresent,currentTag,currentHidden⟩,currentDistinct,currentShort,currentOrder,protections⟩ := rootMetadata
  obtain ⟨activeThread,activeNow⟩ := activeAfter
  have readyThread : readyMachine.threads.activeThread? = some activeThread := by rw [readyFields.2.2.2.2.2.2.2.2];exact activeNow
  have readyMemory : readyMachine.memory = RetagEntry.updatedMemory machine.memory id ⟨entry.kind,result⟩ result.extra := by
    rw [readyFields.1,finalMemory]
    exact GeneralBorrowRawRootCurrentRelease.replacement_eq machine.memory id entry.kind result
  let current : GeneralBorrowRawRootCurrentBoolReturn.Input := {
    options := options,limits := limits,remaining := remaining,span := span,fuel := validityFuel,debugOff := debugOff,validationFuel := validationEq,
    context := ret.context,validationContext := ret.validationContext,accessEq := ret.accessEq,
    validationWidth := ret.validationWidth,validationRuntimeSize := ret.validationRuntimeSize,sameRuntime := ret.sameRuntime,
    width := ret.width,runtimeWidth := ret.runtimeWidth,runtimeSize := ret.runtimeSize,outerAccessEq := ret.outerAccessEq,
    before := ready,size := frameReady.size,location := frameReady.location,value := true,slot0 := frameReady.output,
    immediate := frameReady.immediate,body := frameReady.body.trans callerBody,identity := frameReady.identity.trans identity,
    callee := frameReady.callee.trans callee,noLocalClocks := by rw [frameReady.extra];exact callerClocks,
    continuation := frameReady.continuation.trans ret.continuation,varargs := frameReady.varargs.trans ret.varargs,
    machine := readyMachine,tracker := GeneralBorrowRawAsMutToCopy.held packet,tracked := readyFields.2.1.trans trackerAfter,
    noClocks := readyFields.2.2.2.2.2.2.2.1.trans raceAfter,noBackend := readyFields.2.2.2.2.1.trans backendAfter,
    ghost := readyFields.2.2.2.2.2.1.trans ghostAfter,shallow := readyFields.2.2.2.2.2.2.1.trans shallowAfter,
    unchecked := by rw [readyControl];exact uncheckedCopy,noGc := by rw [readyControl];exact noGcCopy,
    fixed := by change readyMachine.threads.fixedScheduling = true;rw [readyFields.2.2.2.2.2.2.2.2];exact fixedAfter,
    thread := activeThread,active := readyThread,baseline := machine.memory,id := id,entry := ⟨entry.kind,result⟩,tree := result.extra,memoryEq := readyMemory,
    tag := parentTag,anchor := raw.parent,selected := packet.selected,maximum := packet.maximum,offset := offset,len := len,
    runtime := copyRuntime,positive := Classical.choice originalPositive,node := currentNode,present := currentPresent,
    sameTag := currentTag.trans ret.sourceTag,hidden := currentHidden,distinct := currentDistinct,order := currentOrder,short := currentShort,
    activity := by change GeneralBorrowFreshActiveWithin.ActiveWithin result.extra raw.parent .Write offset (offset+len);exact oldActiveAfter,
    slotId := ret.slotId,separate := ret.separate,slot := ret.slot,slotBefore := ret.slotBefore,slotRoot := ret.slotRoot,slotChild := ret.slotChild,
    slotTree := ret.slotTree,slotRootFree := by rw [protections];exact ret.slotRootFree,slotChildHeld := by rw [protections];exact ret.slotChildHeld,
    slotDistinct := ret.slotDistinct,frameTracked := by rw [frameReady.extra];exact ret.frameTracked,
    slotSize := ret.slotSize,slotStorage := ret.slotStorage,slotMask := ret.slotMask,slotProvenance := ret.slotProvenance,slotMutable := ret.slotMutable,
    place := ret.place,layout := ret.layout,slotBase := ret.slotBase,slotPointer := ret.slotPointer,aligned := ret.aligned,fits := ret.fits,
    cached := by rw [readyFields.2.2.1,addresses,outcome.addresses,packetAddresses];exact ret.cached,
    extras := by change readyMachine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [readyFields.2.2.2.1,extrasAfter,outcome.extras,metadataLedger.extras];exact ret.extras,
    destination := by rw [frameReady.destination];exact ret.destination }
  obtain ⟨returned⟩ := GeneralBorrowRawRootCurrentBoolReturn.complete current
  have physicalResult := returned.returned
  have physicalFacts := physicalResult
  dsimp only [GeneralBorrowRawRootBoolReturn.Result] at physicalFacts
  obtain ⟨updated,returnTrace,terminal,_,other⟩ := physicalFacts
  let terminalState := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped returned.physical)
    returned.physical.release.slotId returned.physical.release.slot.kind updated
  have returnTrace' : SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] ready readyMachine) terminalState := by
    simpa only [GeneralBorrowRawRootBoolReturn.caller,returned.options,returned.limits,returned.remaining,returned.span,returned.before,returned.machine] using returnTrace
  have terminal' : ExecutionMachine.step cfg limits () terminalState = (terminalState,.ok false) := by
    simpa only [returned.options,returned.limits,returned.remaining,returned.span] using terminal
  have prefixDone := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace trace') cleanup
  have fullTrace := SuccessfulTrace.append prefixDone returnTrace'
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
  have entryCall : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] caller machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have past : CallSafety.pastCallBoundary 1 terminalState := by change (0:Nat)<1;decide
  have safe := SuccessfulTrace.no_ub safety 1 _ terminalState entryCall fullTrace past
  have physicalTrue : returned.physical.value = true := returned.value
  have encoded : GeneralBorrowRawReturnedBytes.Encoded returned.physical.context updated true := {
    size:=other.2.1.trans returned.physical.slotSize,
    storage:=other.2.2.1.trans returned.physical.slotStorage,
    mask:=by rw [other.2.2.2.1,returned.physical.slotSize],
    provenance:=other.2.2.2.2.1,
    mutable:=other.2.2.2.2.2.2.trans returned.physical.slotMutable,
    width:=returned.physical.runtimeWidth,
    bytes:=by simpa only [returned.physical.slotSize,physicalTrue] using other.2.2.2.2.2.1 }
  exact ⟨returned.physical,returned.value,returned.slotId,physicalResult,updated,fullTrace,terminal',safe,encoded⟩
end
end DuplicatePrefix.GeneralBorrowRawDefaultFullTrueObserved
