import duplicate_prefix.GenericSharedLenAccepted
import duplicate_prefix.GeneralBorrowFreshSharedTwoReleaseWithin
namespace DuplicatePrefix.GenericSharedLenAcceptedStrong
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem after_release (before tree released : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor target : UniIndex) (offset len : UInt64)
    (equation : tree.releaseProtector tag protections=⟨released,.Released⟩)
    (facts : let result := tree.releaseProtector tag protections
      result.status=.Released ∧ result.tree={tree with locations:=result.tree.locations} ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned result.tree protections anchor .Read)
        offset (offset+len) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write offset (offset+len) ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size=before.locations.size) :
    GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
    released.locations.WellFormed ∧ released.locations.size=before.locations.size ∧
    released={tree with locations:=released.locations} := by
  rw [equation] at facts
  exact ⟨facts.2.2.2.1,facts.2.2.2.2.1,facts.2.2.2.2.2,facts.2.1⟩

theorem before_guard_full_data
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
    (roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
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
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25) (all : CopyHelperCleanup.AllImmediate frame)
    (initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len))
 :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
       done.borrowTracker=some ended ∧ done.memory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
       GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
         offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ GenericSharedLenAccepted.RuntimeFacts options remaining span machine done ∧
      GenericSharedLenAccepted.PreGuardFrameFacts frame result len value ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      (let exprTag := tracker.global.nextPointerTag
       let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
       released = {(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree with locations:=released.locations}) := by
  obtain ⟨result,done,released,ended,previous,releaseFacts,runtimeFacts,frameFacts,memoryEq⟩ :=
    GenericSharedLenAccepted.before_guard_data options limits remaining budget dispatchFuel span precise implicitWrites debug cmp
      dynamicFuel validityFuel dynamicEq validationEq id entry base offset len positive nonnull signedFits
      frame machine tracker enabled defaultMode fresh target first capacity owned second secondParent roomData fresh2 different
      v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body identity callee location frameRace race ghost shallow
      cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source rangePositive exprUnheld size all
  let exprTag := tracker.global.nextPointerTag
  let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
  let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
  have pure := GeneralBorrowFreshSharedTwoReleaseWithin.complete_data entry.allocation.extra tracker.global.protectedTags target
    exprTag childTag offset len first second roomData owned rangePositive initialActive
  have strengthened := after_release entry.allocation.extra childTree released
    (GeneralBorrowFreshSharedSequence.registered tracker.global.protectedTags childTag true) childTag
    (GeneralBorrowFreshSharedSequence.index second) target offset len releaseFacts.1 pure
  exact ⟨result,done,released,ended,previous,releaseFacts,runtimeFacts,frameFacts,memoryEq,
    strengthened.1,strengthened.2.1,strengthened.2.2.1,strengthened.2.2.2⟩

theorem before_guard_full
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
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25) (all : CopyHelperCleanup.AllImmediate frame)
    (initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len))
 :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
       done.borrowTracker=some ended ∧ done.memory.live.find? (fun row => row.1 == id)=some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
       GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
         offset (offset+len) released.locations) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ GenericSharedLenAccepted.RuntimeFacts options remaining span machine done ∧
      GenericSharedLenAccepted.PreGuardFrameFacts frame result len value ∧ done.memory=RetagEntry.updatedMemory machine.memory id entry released ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      (let exprTag := tracker.global.nextPointerTag
       let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       released = {(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree with locations:=released.locations}) := by
  have aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295 := by rw [←aligned];exact room
  exact before_guard_full_data options limits remaining budget dispatchFuel span precise implicitWrites debug cmp
      dynamicFuel validityFuel dynamicEq validationEq id entry base offset len positive nonnull signedFits
      frame machine tracker enabled defaultMode fresh target first capacity owned
      (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
        tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
        offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val rfl roomData fresh2 different
      v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body identity callee location frameRace race ghost shallow
      cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source rangePositive exprUnheld size all initialActive

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
    (roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295)
    (fresh2 : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (different : tracker.global.nextPointerTag ≠ (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
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
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)

    (initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)) :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations) ∧
      GenericSharedLenAccepted.RuntimeFacts options remaining span machine done ∧ result.trackCallerArg=frame.trackCallerArg ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      (let exprTag := tracker.global.nextPointerTag
       let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
       released = {(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree with locations:=released.locations}) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ GenericSharedLenAccepted.EndpointFrameFacts frame result ∧
      done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  obtain ⟨result,done,released,ended,previous,releaseFacts,runtimeFacts,track,frameFacts,memoryEq⟩ := GenericSharedLenAccepted.executes_full_data options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned second secondParent roomData
    fresh2 different v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body
    identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
    rangePositive exprUnheld size count countPositive within all live0 cache0 live7 cache7 live8 cache8 live9 cache9 live10 cache10 live13 cache13
    dead15 cache15 dead16 cache16
  let exprTag := tracker.global.nextPointerTag
  let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let childTag := lenTracker.global.nextPointerTag
  let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
  have pure := GeneralBorrowFreshSharedTwoReleaseWithin.complete_data entry.allocation.extra tracker.global.protectedTags target
    exprTag childTag offset len first second roomData owned rangePositive initialActive
  have strengthened := after_release entry.allocation.extra childTree released
    (GeneralBorrowFreshSharedSequence.registered tracker.global.protectedTags childTag true) childTag
    (GeneralBorrowFreshSharedSequence.index second) target offset len releaseFacts.1 pure
  exact ⟨result,done,released,ended,previous,runtimeFacts,track,strengthened.1,strengthened.2.1,strengthened.2.2.1,
    strengthened.2.2.2,releaseFacts,frameFacts,memoryEq⟩

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
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)

    (initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)) :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations) ∧
      GenericSharedLenAccepted.RuntimeFacts options remaining span machine done ∧ result.trackCallerArg=frame.trackCallerArg ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      (let exprTag := tracker.global.nextPointerTag
       let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       released = {(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree with locations:=released.locations}) ∧
      (let exprTag := tracker.global.nextPointerTag
       let lenTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
       let childTag := lenTracker.global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       let childTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
       let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker lenTracker fresh2) childTag
       let borrowFrame := ({} : FrameState).addProtector id childTag
       childTree.releaseProtector childTag held.global.protectedTags = ⟨released,.Released⟩ ∧
       ended = {held with global:=held.global.endCall borrowFrame}) ∧ GenericSharedLenAccepted.EndpointFrameFacts frame result ∧
      done.memory=RetagEntry.updatedMemory machine.memory id entry released := by
  have aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size := by
    cases first.slot with
    | append empty aligned fits => exact aligned
    | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available
  have roomData : entry.allocation.extra.nodes.data.size+1 ≤ 4294967295 := by rw [←aligned];exact room
  exact executes_full_data options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned
    (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target
      tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
      offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val rfl roomData fresh2 different v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body
    identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
    rangePositive exprUnheld size count countPositive within all live0 cache0 live7 cache7 live8 cache8 live9 cache9 live10 cache10 live13 cache13
    dead15 cache15 dead16 cache16 initialActive

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
    (fixed : machine.threads.fixedScheduling = true) (source : PreparedContracts.SourceComparator)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprUnheld : tracker.global.protectedTags.contains tracker.global.nextPointerTag = false)
    (size : frame.locals.size=25)
    (count : UInt64) (countPositive : (0 : UInt64)<count) (within : count≤len/2)
    (all : CopyHelperCleanup.AllImmediate frame)
    (live0 : (frame.locals[0]'(by omega)).value=.live (.immediate .uninit)) (cache0 : (frame.locals[0]'(by omega)).layout=none)
    (live7 : (frame.locals[7]'(by omega)).value=.live (.immediate .uninit)) (cache7 : (frame.locals[7]'(by omega)).layout=none)
    (live8 : (frame.locals[8]'(by omega)).value=.live (.immediate .uninit)) (cache8 : (frame.locals[8]'(by omega)).layout=none)
    (live9 : (frame.locals[9]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache9 : (frame.locals[9]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (live10 : (frame.locals[10]'(by omega)).value=.live (.immediate .uninit)) (cache10 : (frame.locals[10]'(by omega)).layout=none)
    (live13 : (frame.locals[13]'(by omega)).value=.live (.immediate .uninit)) (cache13 : (frame.locals[13]'(by omega)).layout=none)
    (dead15 : (frame.locals[15]'(by omega)).value=.dead) (cache15 : (frame.locals[15]'(by omega)).layout=none)
    (dead16 : (frame.locals[16]'(by omega)).value=.dead) (cache16 : (frame.locals[16]'(by omega)).layout=none)

    (initialActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)) :
    ∃ (result : CompilerFrameContext.ActualFrame) (done : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree) (ended : MachineHooks.BorrowState),
      (SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result done) ∧
      result.location = .mir ⟨6,7⟩ ∧ done.borrowTracker=some ended ∧
      done.memory.live.find? (fun row => row.1 == id) = some (id,GeneralBorrowFreshSharedPop.withTree entry released) ∧
      result.body=frame.body ∧ result.bodyIdentity=frame.bodyIdentity ∧ result.functionInstance=frame.functionInstance ∧
      result.extra=frame.extra ∧ result.locals.size=25 ∧ result.locals[1]?=frame.locals[1]? ∧ result.locals[2]?=frame.locals[2]? ∧
      result.locals[15]?=some ⟨.live (.immediate .uninit),none⟩ ∧ result.locals[16]?=some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned released ended.global.protectedTags target .Write)
        offset (offset+len) released.locations) ∧
      GenericSharedLenAccepted.RuntimeFacts options remaining span machine done ∧ result.trackCallerArg=frame.trackCallerArg ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write offset (offset+len) ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      (let exprTag := tracker.global.nextPointerTag
       let childTag := (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
       let second := (GeneralBorrowFreshSharedNext.next entry.allocation.extra tracker.global.protectedTags target exprTag childTag
         offset len first noFree room tagFresh protectorFresh different cleanFuture owned).val
       released = {(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree with locations:=released.locations}) := by
  obtain ⟨result,done,released,ended,previous,runtimeFacts,track,targetActive,well,capacity,treeFrame,_,_,_⟩ := executes_full options limits remaining budget dispatchFuel span precise implicitWrites debug cmp dynamicFuel validityFuel dynamicEq validationEq
    id entry base offset len positive nonnull signedFits frame machine tracker enabled defaultMode fresh target first capacity owned noFree room
    fresh2 tagFresh protectorFresh different cleanFuture v1 v11 v12 sourceLive sourceCached lenLive lenUncached exprLive exprUncached body
    identity callee location frameRace race ghost shallow cached present metadata notConstructed backend thread active threadCache unchecked noGc fixed source
    rangePositive exprUnheld size count countPositive within all live0 cache0 live7 cache7 live8 cache8 live9 cache9 live10 cache10 live13 cache13
    dead15 cache15 dead16 cache16 initialActive
  exact ⟨result,done,released,ended,previous,runtimeFacts,track,targetActive,well,capacity,treeFrame⟩

end
end DuplicatePrefix.GenericSharedLenAcceptedStrong
