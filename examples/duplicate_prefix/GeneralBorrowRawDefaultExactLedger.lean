import duplicate_prefix.GeneralBorrowRawAsMutCopyLedger
import duplicate_prefix.GeneralBorrowRawAsMutCallerExactLedger
import duplicate_prefix.GeneralBorrowRawDefaultResources
namespace DuplicatePrefix.GeneralBorrowRawDefaultExactLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
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
    (unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ packet : GeneralBorrowRawAsMutToCopy.Input, ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller machine)
        (Storage.withCurrent #[] result finalMachine) ∧
      packet.tag = (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ∧ packet.count = count ∧
      PositiveRootSuccessProfile.FrameShape packet.caller result (GeneralBorrowRawAsMutToCopy.pointer packet)
        (Scalar.fromPointer cfg.access.runtime.base
          (Pointer.new (.concrete id packet.tag) (Size.ofBytes (base+offset+count)))) count ∧
      finalMachine.memory = GeneralBorrowRawAsMutToCopy.memory packet ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held packet) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts
        (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held packet).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive
        (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags
        (some packet.anchor) (some packet.selected) packet.maximum packet.offset packet.len) ∧
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree.indexOfTag packet.tag = some packet.anchor ∧
      GeneralBorrowRawAsMutCopyLedger.Metadata entry machine id base offset len count packet ∧
      GeneralBorrowRawAsMutCopyLedger.Outcome packet finalMachine ∧
      ∃ secondFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615,
        GeneralBorrowRawAsMutCopyLedger.Resources
          (GeneralBorrowRawFnEntryArgument.finalTree
            (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags
              parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
            (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag offset len)
          (TypedBorrowSteps.registeredTracker
            (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) secondFresh)
            (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
          (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag packet ∧
          GeneralBorrowRawAsMutCopyLedger.Configuration options limits remaining span validityFuel packet ∧
          packet.caller = AsMutUncachedCall.cachedCaller
            (CopyHelperSteps.advance (ActualLocalCopy.written caller 16 (RootReferenceInfo.layout false) valid16
              (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
                (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (RootReferenceInfo.layout false)).imm) ⟨6,7⟩)
            (by simpa only [CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using destValid) ∧
          packet.machine.memory = RetagEntry.updatedMemory machine.memory id entry packet.entry.allocation.extra ∧
          packet.machine.user.addresses = machine.user.addresses := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let finalTree := (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags
    parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  let allocated := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let childValue := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (RootReferenceInfo.layout false)).imm
  let afterFrame := CopyHelperSteps.advance
    (ActualLocalCopy.written caller 16 (RootReferenceInfo.layout false) valid16 childValue) ⟨6,7⟩
  let afterMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have step := GeneralBorrowRawDefaultExpression.positive_statement options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq base offset len id entry positive nonzero signedFits #[] caller machine
    callerBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
    valid1 valid16 source1 cached1 dead16 uncached16 callerClocks ghost shallow cachedAddress present race metadata notConstructed
  have resources := GeneralBorrowRawDefaultResources.resources entry.allocation.extra tracker runtime raw headroom tagsRoom
  dsimp only at resources
  have treeEq : (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags
      raw.parentTag tracker.global.nextPointerTag raw.offset raw.len .VisitChildrenOfAccessed).tree = finalTree := by
    rw [rawTag,rawOffset,rawLen]
  rw [treeEq] at resources
  simp only [rawTag,rawOffset,rawLen] at resources
  obtain ⟨afterRuntime,afterCapacity,afterHeadroom,next,nextTag,nextSelected,nextMaximum,nextOffset,nextLen⟩ := resources
  have afterSize : afterFrame.locals.size = caller.locals.size := by simp only [afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set]
  have other (slot : Nat) (different : slot ≠ 16) : afterFrame.locals[slot]? = caller.locals[slot]? := by
    simp only [afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,different,Ne.symm different,↓reduceIte]
  have otherValue (slot : Nat) (valid : slot < caller.locals.size) (different : slot ≠ 16) :
      afterFrame.locals[slot]'(by rw [afterSize];exact valid) = caller.locals[slot]'valid :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [afterSize];exact valid)).symm.trans
      ((other slot different).trans (Array.getElem?_eq_getElem valid)))
  have afterValid : 15 < afterFrame.locals.size := by rw [afterSize];exact destValid
  have after16 : 16 < afterFrame.locals.size := by rw [afterSize];exact valid16
  have afterPresent : afterMachine.memory.live.find? (fun row => row.1 == id) = some (id,afterEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id afterEntry
  have afterTop : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates
      (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller afterFrame afterValid)
        (AsMutPtrReturn.accountedMachine options remaining span afterMachine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller afterFrame afterValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack
        thread.topUserRelevantFrame = some 0 := by rw [threadTop];rfl
  have afterTopPresent : (AsMutPush.pushed options.userRelevantCrates
      (Storage.withCurrent #[] (AsMutUncachedCall.cachedCaller afterFrame afterValid)
        (AsMutPtrReturn.accountedMachine options remaining span afterMachine))
      (LocalPlaces.localRuntimePlace 0 (AsMutUncachedCall.cachedCaller afterFrame afterValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[0]? =
        some (AsMutUncachedCall.cachedCaller afterFrame afterValid) := by rfl
  obtain ⟨packet,result,finalMachine,trace,packetCaller,packetTag,packetCount,shape,memory,tracked,postRuntime,postPositive,postTagged,packetMetadata,outcome,resourceLedger,configuration,packetMemory,packetAddresses⟩ :=
    GeneralBorrowRawAsMutCallerExactLedger.invoke options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id afterEntry base offset len tracker.global.nextPointerTag positive nonzero signedFits bounds afterFrame afterMachine allocated rfl defaultMode
      next.tagRoom afterRuntime next nextTag nextOffset nextLen (afterCapacity.trans capacity)
      afterValid (by rw [otherValue 15 destValid (by decide)];exact destLive)
      (by rw [otherValue 15 destValid (by decide)];exact uncached) callerClocks ghost shallow cachedAddress afterPresent race metadata notConstructed
      thread 0 (AsMutUncachedCall.cachedCaller afterFrame afterValid) active afterTop afterTopPresent
      afterHeadroom source budget dispatch backend unchecked noGc fixed threadTop
      (afterSize.trans size) callerBody identity callee track relevant
      (CopyHelperCleanup.all_immediate_written caller 16 (RootReferenceInfo.layout false) childValue valid16 immediate)
      rfl after16 (by simp only [afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self];rfl)
      (by simp only [afterFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self];rfl)
      count countPositive within (by rw [other 2 (by decide)];exact slot2) (by rw [other 13 (by decide)];exact slot13)
      (by intro slot lower upper;rw [other slot (by omega)];exact unused slot lower upper)
  have shape' : PositiveRootSuccessProfile.FrameShape packet.caller result (GeneralBorrowRawAsMutToCopy.pointer packet)
      (Scalar.fromPointer cfg.access.runtime.base (Pointer.new (.concrete id packet.tag) (Size.ofBytes (base+offset+count)))) count := by
    rw [packetCaller,packetTag]
    exact shape
  have entryEq : packet.entry = {entry with allocation := entry.allocation.setExtra packet.entry.allocation.extra} := by
    rw [packetMetadata.entry]
    rfl
  have packetMemory' : packet.machine.memory = RetagEntry.updatedMemory machine.memory id entry packet.entry.allocation.extra := by
    rw [packetMemory]
    change RetagEntry.updatedMemory (RetagEntry.updatedMemory machine.memory id entry finalTree) id afterEntry packet.entry.allocation.extra = _
    exact RetagEntry.updated_memory_twice machine.memory id entry finalTree packet.entry.allocation.extra
  exact ⟨packet,result,finalMachine,SuccessfulTrace.Trace.next step trace,packetTag,packetCount,shape',memory,tracked,postRuntime,postPositive,postTagged,
    ⟨packetMetadata.idEq,packetMetadata.baseEq,packetMetadata.offsetEq,packetMetadata.lenEq,packetMetadata.countEq,entryEq,packetMetadata.extras⟩,outcome,next.tagRoom,resourceLedger,configuration,packetCaller,packetMemory',packetAddresses⟩
end
end DuplicatePrefix.GeneralBorrowRawDefaultExactLedger
