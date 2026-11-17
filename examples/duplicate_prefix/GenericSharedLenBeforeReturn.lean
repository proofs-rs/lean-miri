import duplicate_prefix.GenericRootSharedBorrow
import duplicate_prefix.GenericLenBeforeReturn

/-! The actual shared-reference statement and len call/helper body compose from
one caller-owned tree and initial allocator data. The endpoint is immediately
before the len return; release and resumed mutable access are separate. -/
namespace DuplicatePrefix.GenericSharedLenBeforeReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem executes_full_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = tracker.global.nextPointerTag)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator) :
    let exprTag := tracker.global.nextPointerTag
    let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let childTag := lenTracker.global.nextPointerTag
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let exprFrame := CopyHelperSteps.advance
      (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout v12 value) ⟨2,11⟩
    let caller := LenUncachedFrontend.cachedCaller exprFrame
      (by simpa [exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11)
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[caller] result done) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id childTag) ∧ result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 caller 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      done.memory = RetagEntry.updatedMemory machine.memory id entry
        (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree ∧
      done.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag) ∧
      done.user.payload.ghost = false ∧ done.user.payload.validation = .Shallow ∧ done.dataRace = none ∧
      done.user.addresses = machine.user.addresses ∧
      done.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      done.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ) ∧ GenericLenBeforeReturn.ReturnFacts options remaining span result done len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id childTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ GenericLenBeforeReturn.RootCache #[] done := by
  let exprTag := tracker.global.nextPointerTag
  let exprTree := (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
  let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let callFrame := CopyHelperSteps.advance
    (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout v12 value) ⟨2,11⟩
  let exprMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry exprTree}
  let exprEntry := {entry with allocation := entry.allocation.setExtra exprTree}
  let callMachine := PtrMetadataReturn.accountedMachine options remaining span exprMachine
  have expr := GenericRootSharedBorrow.positive_statement options limits remaining span precise implicitWrites debug cmp
    dynamicFuel validityFuel dynamicEq validationEq base offset len id entry positive nonnull signedFits #[] frame machine
    body identity callee location tracker enabled defaultMode fresh target first capacity owned v1 v12 sourceLive sourceCached
    exprLive exprUncached frameRace ghost shallow cached present race metadata notConstructed
  have expr' : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] frame machine) =
      (Storage.withCurrent #[] callFrame exprMachine,.ok true) := expr
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  have callValid : 11 < callFrame.locals.size := by
    simpa [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11
  have sourceValid : 12 < callFrame.locals.size := by
    simpa [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v12
  have callLive : callFrame.locals[11].value = .live (.immediate .uninit) := by
    simpa [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenLive
  have callUncached : callFrame.locals[11].layout = none := by
    simpa [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenUncached
  have callSource : callFrame.locals[12].value = .live (.immediate value) := by
    simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  have callCached : callFrame.locals[12].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [callFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout]
  let caller := LenUncachedFrontend.cachedCaller callFrame callValid
  let destination := (LocalPlaces.localRuntimePlace 0 caller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] caller callMachine
  have top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack
      thread.topUserRelevantFrame = some 0 := by simp [FrameRelevance.top,threadCache]
  have current : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some caller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have callGhost : callMachine.user.payload.ghost = false := by
    rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have callValidation : callMachine.user.payload.validation = .Shallow := by
    rw [PtrMetadataReturn.accounted_validation];exact shallow
  have callAddresses : callMachine.user.addresses = machine.user.addresses := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have callCachedAddress : callMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [callAddresses];exact cached
  have callBackend : callMachine.user.payload.payload.user.backend = .none := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have callPresent : callMachine.memory.live.find? (fun row => row.1 == id) = some (id,exprEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id exprEntry
  have combined : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowFreshReleaseMixed.Combined entry.allocation.extra tracker.global.protectedTags target (fun _ => true))
      offset (offset+len) entry.allocation.extra.locations := by
    intro position valid nonempty lower upper
    exact GeneralBorrowFreshMixedChild.write_combined entry.allocation.extra _ tracker.global.protectedTags target
      (owned position valid nonempty lower upper)
  let stage := GeneralBorrowFreshStageMetadata.build entry.allocation.extra exprTag target offset len first
    tracker.global.protectedTags false (fun _ => true) combined
  have exprCapacity : exprEntry.allocation.extra.locations.size = exprEntry.allocation.byteSize := stage.capacity.trans capacity
  have postMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination caller)).metadata =
      PreparedReflection.actual.runtime := by
    change (LenPushFacts.posted options remaining span #[] caller exprMachine caller).user.payload.payload.user.types.metadata = _
    rw [LenPushFacts.types_eq];exact metadata
  have postNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination caller)).entries.any
      (·.value.ty == 4) = false := by
    change ((LenPushFacts.posted options remaining span #[] caller exprMachine caller).user.payload.payload.user.types.entries.any
      (·.value.ty == 4)) = false
    rw [LenPushFacts.types_eq];exact notConstructed
  obtain ⟨result,done,properties,details,rootCache⟩ :=
    GenericLenBeforeReturn.before_return_full_data options limits remaining budget dispatchFuel span ctx debug cmp
      dynamicFuel validityFuel dynamicEq validationEq id exprEntry base offset len entry.allocation.extra target exprTag
      positive nonnull signedFits #[] callFrame callMachine lenTracker rfl defaultMode fresh2
      first second secondParent owned rfl exprCapacity callValid callLive callUncached
      frameRace callGhost callValidation callCachedAddress callPresent race thread 0 caller active top current postMetadata postNotConstructed
      body identity callee rfl source sourceValid callSource callCached callBackend exprMachine rfl unchecked noGc fixed
  rcases properties with ⟨trace,loc,retval,held,clocks,returnPlace,continuation,va,memoryEq,tracked,dg,dv,dr,da,dt,de⟩
  refine ⟨result,done,?_,details,rootCache⟩
  refine ⟨.next expr' trace,loc,retval,held,clocks,returnPlace,continuation,va,?_,tracked,dg,dv,dr,?_,?_,?_⟩
  · rw [memoryEq]
    exact RetagEntry.updated_memory_twice machine.memory id entry exprTree _
  · exact da
  · exact dt
  · exact de
theorem executes_full
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator) :
    let exprTag := tracker.global.nextPointerTag
    let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let childTag := lenTracker.global.nextPointerTag
    let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      exprTag childTag offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let exprFrame := CopyHelperSteps.advance
      (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout v12 value) ⟨2,11⟩
    let caller := LenUncachedFrontend.cachedCaller exprFrame
      (by simpa [exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11)
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[caller] result done) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id childTag) ∧ result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 caller 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      done.memory = RetagEntry.updatedMemory machine.memory id entry
        (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree ∧
      done.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag) ∧
      done.user.payload.ghost = false ∧ done.user.payload.validation = .Shallow ∧ done.dataRace = none ∧
      done.user.addresses = machine.user.addresses ∧
      done.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      done.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ) ∧ GenericLenBeforeReturn.ReturnFacts options remaining span result done len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id childTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ GenericLenBeforeReturn.RootCache #[] done := by
  exact executes_full_data options limits remaining budget dispatchFuel span precise implicitWrites
    debug cmp dynamicFuel validityFuel dynamicEq validationEq id entry base offset len positive nonnull signedFits
    frame machine tracker enabled defaultMode fresh target first capacity owned
    (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val rfl fresh2 v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body identity callee
    location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc
    fixed source

theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (positive : (0 : UInt64) < len) (nonnull : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (target : UniIndex)
    (first : GeneralBorrowFreshSharedSequence.Data entry.allocation.extra tracker.global.nextPointerTag target offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned entry.allocation.extra tracker.global.protectedTags target .Write)
      offset (offset+len) entry.allocation.extra.locations)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (room : entry.allocation.extra.tagMapping.mapping.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (protectorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshSharedNext.future entry.allocation.extra) = none) entry.allocation.extra.locations)
    (v1 : 1 < frame.locals.size) (v11 : 11 < frame.locals.size) (v12 : 12 < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id first.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (lenLive : frame.locals[11].value = .live (.immediate .uninit)) (lenUncached : frame.locals[11].layout = none)
    (exprLive : frame.locals[12].value = .live (.immediate .uninit)) (exprUncached : frame.locals[12].layout = none)
    (body : frame.body = RootBody.reflected.body.body) (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) (location : frame.location = .mir ⟨2,11⟩)
    (frameRace : frame.extra.dataRace = none) (race : machine.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (backend : machine.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (threadCache : thread.topUserRelevantFrame = some 0)
    (unchecked : ((config options (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator) :
    let exprTag := tracker.global.nextPointerTag
    let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let childTag := lenTracker.global.nextPointerTag
    let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      exprTag childTag offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let exprFrame := CopyHelperSteps.advance
      (ActualLocalCopy.written frame 12 SharedReferenceMetadata.sharedLayout v12 value) ⟨2,11⟩
    let caller := LenUncachedFrontend.cachedCaller exprFrame
      (by simpa [exprFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using v11)
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[caller] result done) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id childTag) ∧ result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace 0 caller 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      done.memory = RetagEntry.updatedMemory machine.memory id entry
        (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree ∧
      done.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag) ∧
      done.user.payload.ghost = false ∧ done.user.payload.validation = .Shallow ∧ done.dataRace = none ∧
      done.user.addresses = machine.user.addresses ∧
      done.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      done.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  obtain ⟨result,done,properties,_,_⟩ := executes_full options limits remaining budget dispatchFuel span precise implicitWrites
    debug cmp dynamicFuel validityFuel dynamicEq validationEq id entry base offset len positive nonnull signedFits
    frame machine tracker enabled defaultMode fresh target first capacity owned noFree room fresh2 tagFresh protectorFresh
    different cleanFuture v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body identity callee
    location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc
    fixed source
  exact ⟨result,done,properties⟩

end
end DuplicatePrefix.GenericSharedLenBeforeReturn
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GenericSharedLenBeforeReturn.executes,``DuplicatePrefix.GenericSharedLenBeforeReturn.executes_full] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved shared-expression/len runtime dependency {dependency}"
