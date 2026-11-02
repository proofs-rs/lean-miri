import duplicate_prefix.GeneralBorrowExposedScopedLenBeforeReturn
import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedReadRelease
import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedData
import duplicate_prefix.LenReturnFromReleaseRuntime
import duplicate_prefix.GenericSharedLenAccepted
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableLenCallReturnRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
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
    (raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources input
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable)
    (treeEq : input.tree=entry.allocation.extra) (parentTagEq : input.parentTag=exprTag)
    (tagEq : input.newTag=tracker.global.nextPointerTag) (offsetEq : input.offset=offset) (lenEq : input.len=len)
    (protectedEq : input.isProtected=true) (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
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
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedWritableReadData.Data released location held.global.protectedTags
        (GeneralBorrowFreshMetadataChildShared.index input) selected head tail
        (fun position => raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildShared.index input).toNat)))
        offset (offset+len) released.locations ∧
      released.locations.WellFormed ∧ released.locations.size=entry.allocation.extra.locations.size ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span beforeMachine post ∧
      (frames=#[] → GenericSharedLenAccepted.RuntimeFacts options remaining span beforeMachine post) := by
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedWritableSharedData.build input
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable raw
  have mixedOwned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data input.tree location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags input.parent selected head tail raw.component.support writable)) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩:=owned position valid positive lower upper
    exact ⟨data.base⟩
  rw [treeEq] at context
  simp only [treeEq,offsetEq,lenEq] at mixedOwned
  have forest : GeneralBorrowForest.Forest (source_normal_projection entry.allocation.extra default tracker.global.protectedTags).topology := by
    rw [←treeEq]
    exact raw.forest
  let root := cachedCaller caller valid
  let childTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  obtain ⟨helper,atReturn,properties,facts,rootCache⟩ := GeneralBorrowExposedScopedLenBeforeReturn.before_return_full_data options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    input.parent selected head tail context (by rw [←treeEq];exact input.covered) forest
    (by rw [←treeEq,←parentTagEq];exact input.parentTagPresent) (by rw [←treeEq,←tagEq];exact input.fresh)
    (by rw [←treeEq];exact input.noFree) (by rw [←treeEq];exact input.aligned) (by rw [←treeEq];exact input.fits)
    raw.component.support writable (by rw [←treeEq];exact input.well) mixedOwned allocationSize valid live uncached noClocks ghost shallow
    cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
  rcases properties with ⟨prefixTrace,helperLocation,retval,helperTracked,helperRace,destination,continuation,varargs,
    memoryEq,heldEq,ghostEq,shallowEq,raceEq,addressesEq,typesEq,extrasEq⟩
  have release := GeneralBorrowExposedScopedWritableSharedReadRelease.release input
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags selected head tail writable raw atBase full rangePositive clean
  simp only [treeEq,parentTagEq,tagEq,offsetEq,lenEq,protectedEq] at release
  change (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).status=.Released ∧
    GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedWritableReadData.Data
      (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree location held.global.protectedTags
      (GeneralBorrowFreshMetadataChildShared.index input) selected head tail
      (fun position => raw.component.support position ∨ position=(GeneralBorrowFreshMetadataChildShared.index input).toNat)
      (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildShared.index input).toNat)))
      offset (offset+len) (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree.locations ∧
    (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree.locations.WellFormed ∧
    (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree.locations.size=entry.allocation.extra.locations.size at release
  let released := (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  have complete : childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags=⟨released,.Released⟩ := by
    dsimp only [released]
    cases eqn : childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags with
    | mk tree status => have done:=release.1;rw [eqn] at done;cases done;rfl
  have callerValid : (11 : MIR.LocalId)<root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have callerLive : root.locals[11].value=.live (.immediate .uninit) := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have callerCached : root.locals[11].layout=some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  obtain ⟨finalRoot,post,step,rootEq,memoryFinal,trackedFinal,runtime,cache⟩ := LenReturnFromReleaseRuntime.step options limits remaining span debugOff validityFuel validationEq
    frames root helper atReturn len _ facts helperLocation retval helperRace destination continuation varargs callerValid callerLive callerCached noClocks
    id tracker.global.nextPointerTag entry childTree released beforeMachine.memory memoryEq held borrowFrame heldEq helperTracked rfl complete rootCache raceEq ghostEq shallowEq
  have finalRuntime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span beforeMachine post := {
    runtime with addresses:=runtime.addresses.trans addressesEq,types:=runtime.types.trans typesEq,extras:=runtime.extras.trans extrasEq }
  have rootRuntime : frames=#[] → GenericSharedLenAccepted.RuntimeFacts options remaining span beforeMachine post := by
    intro empty
    exact ⟨finalRuntime.ghost,finalRuntime.shallow,finalRuntime.race,finalRuntime.addresses,finalRuntime.types,finalRuntime.extras,
      finalRuntime.backend,finalRuntime.unchecked,finalRuntime.noGc,finalRuntime.fixed,cache empty⟩
  exact ⟨finalRoot,post,released,SuccessfulTrace.append prefixTrace (.next step (.refl _)),rootEq,memoryFinal,trackedFinal,complete,
    release.2.1,release.2.2.1,release.2.2.2,finalRuntime,rootRuntime⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedWritableLenCallReturnRuntime
