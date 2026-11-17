import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableLenCallReturnRuntime
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedCallReady
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenCallReturnReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual len call/body/return/pop/endCall reaches caller PC3:0 and forms the
older target Write contract on the allocation actually stored in the returned
machine. Initial physical/source resources suffice; no helper poststate,
Write-ready contract, cache coherence, or successful release is an input. -/
theorem executes
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (input : GeneralBorrowFreshMetadataChildShared.Input) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.Resources input
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable)
    (treeEq : input.tree=entry.allocation.extra) (parentTagEq : input.parentTag=exprTag)
    (tagEq : input.newTag=tracker.global.nextPointerTag) (offsetEq : input.offset=offset) (lenEq : input.len=len)
    (protectedEq : input.isProtected=true)
    (rangePositive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildShared.index input)=none) input.tree.locations)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (first : GeneralBorrowFreshMetadataChildShared.Input) (firstTags : ProtectedTags)
    (firstRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.Resources first firstTags selected head tail (fun _=>true))
    (firstTreeEq : input.tree=GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child first firstTags .VisitChildrenOfAccessed)
    (firstParentEq : input.parent=GeneralBorrowFreshMetadataChildShared.index first)
    (writableEq : writable=GeneralBorrowFreshMixedChild.extend (fun _=>true) (GeneralBorrowFreshMetadataChildShared.index first).toNat)
    (initialTags : GeneralBorrowGcAllocator.NodeTags first.tree)
    (exprUnheld : (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags.contains input.parentNode.tag=false)

 :
    let childTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (released : BorrowTree),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine) (Storage.withCurrent frames root post) ∧
      root={writeFrame (cachedCaller caller valid) 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
        (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags=⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released location held.global.protectedTags
        (GeneralBorrowFreshMetadataChildShared.index input) selected head tail
        (fun position => raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildShared.index input).toNat)))
        offset (offset+len) released.locations ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span beforeMachine post ∧
      (frames=#[] → GenericSharedLenAccepted.RuntimeFacts options remaining span beforeMachine post) ∧
      post.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) ∧
      GeneralBorrowGcAllocator.NodeTags released ∧
      ∃ writeContext : GeneralBorrowExposedKnownRootRangeData.Context released first.parent selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released location
          (held.global.endCall borrowFrame).protectedTags first.parent selected head tail
          (fun position=>raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat) (fun _=>true)))
          offset (offset+len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
          (held.global.endCall borrowFrame).protectedTags) offset (offset+len) released.locations := by
  obtain ⟨root,post,released,trace,rootEq,memoryEq,trackerEq,complete,postData,well,size,runtime,rootRuntime⟩:=
    GeneralBorrowExposedScopedInactiveWritableLenCallReturnRuntime.executes options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    input selected head tail writable raw treeEq parentTagEq tagEq offsetEq lenEq protectedEq rangePositive clean allocationSize
    valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed
    sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  let held:=TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame:=({} : FrameState).addProtector id tracker.global.nextPointerTag
  let childTree:=GeneralBorrowExposedScopedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
  let helperRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.Resources input held.global.protectedTags selected head tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (GeneralBorrowFreshMetadataChildShared.index first).toNat) := by
    rw [←writableEq]
    exact raw
  have childEq : GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed=childTree := by
    simp only [GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child,GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,
      treeEq,parentTagEq,tagEq,offsetEq,lenEq,protectedEq]
    rfl
  have sourceReleased : ((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag held.global.protectedTags).tree=released := by
    rw [childEq,tagEq,complete]
  obtain ⟨writeContext,targetWritable⟩:=GeneralBorrowExposedScopedInactiveWritableSharedCallReady.build first input firstTags held.global id selected head tail firstRaw helperRaw
    firstTreeEq firstParentEq initialTags exprUnheld rangePositive clean
  rw [sourceReleased] at writeContext
  rw [sourceReleased,tagEq,offsetEq,lenEq] at targetWritable
  have helperSupport : helperRaw.component.support=raw.component.support := by
    dsimp only [helperRaw]
    cases writableEq
    rfl
  rw [helperSupport] at targetWritable
  have firstMetadata:=GeneralBorrowExposedScopedInactiveWritableSharedMetadata.run first firstTags selected head tail (fun _=>true) firstRaw initialTags
  have helperTags : GeneralBorrowGcAllocator.NodeTags input.tree := by rw [firstTreeEq];exact firstMetadata.1
  have helperMetadata:=GeneralBorrowExposedScopedInactiveWritableSharedMetadata.run input held.global.protectedTags selected head tail _ helperRaw helperTags
  have finalTags : GeneralBorrowGcAllocator.NodeTags released := by
    have good:=helperMetadata.2.1
    change GeneralBorrowGcAllocator.NodeTags ((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag held.global.protectedTags).tree at good
    rw [sourceReleased] at good
    exact good
  have finalPresent : post.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) := by
    rw [memoryEq]
    exact MemoryCopyBridge.live_lookup_replaced beforeMachine.memory id _
  have coherent : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
      (held.global.endCall borrowFrame).protectedTags) offset (offset+len) released.locations := by
    intro position bounded positive lower upper
    obtain ⟨data⟩:=targetWritable position bounded positive lower upper
    exact data.base.base.coherent
  exact ⟨root,post,released,trace,rootEq,memoryEq,trackerEq,complete,postData,well,size,runtime,rootRuntime,
    finalPresent,finalTags,writeContext,targetWritable,coherent⟩

/-- Actual len-call return for either profile mode, without global-profile recovery. -/
theorem executes_mode {profileMode : ProfileMode}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (input : GeneralBorrowFreshMetadataChildShared.Input) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable profileMode)
    (treeEq : input.tree=entry.allocation.extra) (parentTagEq : input.parentTag=exprTag)
    (tagEq : input.newTag=tracker.global.nextPointerTag) (offsetEq : input.offset=offset) (lenEq : input.len=len)
    (protectedEq : input.isProtected=true)
    (rangePositive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildShared.index input)=none) input.tree.locations)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 11 < caller.locals.size)
    (live : caller.locals[11].value = .live (.immediate .uninit))
    (uncached : caller.locals[11].layout = none)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false)
    (sourceBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨2,12⟩)
    (source : PreparedContracts.SourceComparator)
    (sourceValid : 12 < caller.locals.size)
    (sourceLive : caller.locals[12].value = .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm))
    (sourceCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout)
    (backend : machine.user.payload.payload.user.backend = .none)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = PtrMetadataReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true)
    (first : GeneralBorrowFreshMetadataChildShared.Input) (firstTags : ProtectedTags)
    (firstRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor first firstTags selected head tail (fun _=>true) profileMode)
    (firstTreeEq : input.tree=GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child first firstTags .VisitChildrenOfAccessed)
    (firstParentEq : input.parent=GeneralBorrowFreshMetadataChildShared.index first)
    (writableEq : writable=GeneralBorrowFreshMixedChild.extend (fun _=>true) (GeneralBorrowFreshMetadataChildShared.index first).toNat)
    (initialTags : GeneralBorrowGcAllocator.NodeTags first.tree)
    (exprUnheld : (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags.contains input.parentNode.tag=false)

 :
    let childTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (released : BorrowTree),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine) (Storage.withCurrent frames root post) ∧
      root={writeFrame (cachedCaller caller valid) 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
        (by simpa [cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags=⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released location held.global.protectedTags
        (GeneralBorrowFreshMetadataChildShared.index input) selected head tail
        (fun position => raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildShared.index input).toNat)))
        offset (offset+len) released.locations ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span beforeMachine post ∧
      (frames=#[] → GenericSharedLenAccepted.RuntimeFacts options remaining span beforeMachine post) ∧
      post.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) ∧
      GeneralBorrowGcAllocator.NodeTags released ∧
      ∃ writeContext : GeneralBorrowExposedKnownRootRangeData.Context released first.parent selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released location
          (held.global.endCall borrowFrame).protectedTags first.parent selected head tail
          (fun position=>raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat) (fun _=>true)))
          offset (offset+len) released.locations ∧
        GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
          (held.global.endCall borrowFrame).protectedTags) offset (offset+len) released.locations := by
  obtain ⟨root,post,released,trace,rootEq,memoryEq,trackerEq,complete,postData,well,size,runtime,rootRuntime⟩:=
    GeneralBorrowExposedScopedInactiveWritableLenCallReturnRuntime.executes_mode options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    input selected head tail writable raw treeEq parentTagEq tagEq offsetEq lenEq protectedEq rangePositive clean allocationSize
    valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed
    sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  let held:=TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame:=({} : FrameState).addProtector id tracker.global.nextPointerTag
  let childTree:=GeneralBorrowExposedScopedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
  let helperRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input held.global.protectedTags selected head tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (GeneralBorrowFreshMetadataChildShared.index first).toNat) profileMode := by
    rw [←writableEq]
    exact raw
  have childEq : GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed=childTree := by
    simp only [GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child,GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,
      treeEq,parentTagEq,tagEq,offsetEq,lenEq,protectedEq]
    rfl
  have sourceReleased : ((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag held.global.protectedTags).tree=released := by
    rw [childEq,tagEq,complete]
  obtain ⟨writeContext,targetWritable⟩:=GeneralBorrowExposedScopedInactiveWritableSharedCallReady.build first input firstTags held.global id selected head tail firstRaw helperRaw
    firstTreeEq firstParentEq initialTags exprUnheld rangePositive clean
  rw [sourceReleased] at writeContext
  rw [sourceReleased,tagEq,offsetEq,lenEq] at targetWritable
  have helperSupport : helperRaw.component.support=raw.component.support := by
    dsimp only [helperRaw]
    cases writableEq
    rfl
  rw [helperSupport] at targetWritable
  have firstMetadata:=GeneralBorrowExposedScopedInactiveWritableSharedMetadata.run first firstTags selected head tail (fun _=>true) firstRaw initialTags
  have helperTags : GeneralBorrowGcAllocator.NodeTags input.tree := by rw [firstTreeEq];exact firstMetadata.1
  have helperMetadata:=GeneralBorrowExposedScopedInactiveWritableSharedMetadata.run input held.global.protectedTags selected head tail _ helperRaw helperTags
  have finalTags : GeneralBorrowGcAllocator.NodeTags released := by
    have good:=helperMetadata.2.1
    change GeneralBorrowGcAllocator.NodeTags ((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input held.global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag held.global.protectedTags).tree at good
    rw [sourceReleased] at good
    exact good
  have finalPresent : post.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra released}) := by
    rw [memoryEq]
    exact MemoryCopyBridge.live_lookup_replaced beforeMachine.memory id _
  have coherent : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location
      (held.global.endCall borrowFrame).protectedTags) offset (offset+len) released.locations := by
    intro position bounded positive lower upper
    obtain ⟨data⟩:=targetWritable position bounded positive lower upper
    exact data.base.base.coherent
  exact ⟨root,post,released,trace,rootEq,memoryEq,trackerEq,complete,postData,well,size,runtime,rootRuntime,
    finalPresent,finalTags,writeContext,targetWritable,coherent⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenCallReturnReady
