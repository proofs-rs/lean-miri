import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnFull
import duplicate_prefix.GeneralBorrowForestMixedSharedRestoredResources
import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnRuntime
import duplicate_prefix.GeneralBorrowForestMixedSharedRestoreData
namespace DuplicatePrefix.GeneralBorrowForestMixedLenCallReturnResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 65536
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
    (parent primary : UniIndex) (extras : List UniIndex)
    (context : GeneralBorrowForestAccessData.Context entry.allocation.extra parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (tagPresent : entry.allocation.extra.indexOfTag exprTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, entry.allocation.extra.nodeAt index = some node → entry.allocation.extra.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot entry.allocation.extra context.depth parent)
    (fits : entry.allocation.extra.nodes.data.size ≤ 4294967296)
    (well : entry.allocation.extra.locations.WellFormed)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) entry.allocation.extra.locations)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data entry.allocation.extra location tracker.global.protectedTags parent primary extras (GeneralBorrowFreshMixedChild.extend (fun _ => true) parent.toNat)))
      offset (offset+len) entry.allocation.extra.locations)
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
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : entry.allocation.extra.nodeAt target = some targetNode)
    (exprFree : tracker.global.protectedTags.contains context.anchorNode.tag = false)
    (prefixPath : ∀ location, (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath parent.toNat =
      parent.toNat :: (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location, parent.toNat ∉ (source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat)
    (rootPath : ∀ location, ((source_normal_projection entry.allocation.extra location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)) :
    let initialRoot := cachedCaller caller valid
    let childTree := GeneralBorrowForestMixedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (released : BorrowTree),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine) (Storage.withCurrent frames root post) ∧
      root = {writeFrame initialRoot 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
        (by simpa [initialRoot,cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location := .mir ⟨3,0⟩} ∧
      post.memory = RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker = some {held with global := held.global.endCall borrowFrame} ∧
      childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags = ⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data released location (held.global.endCall borrowFrame).protectedTags
          target primary extras)) offset (offset+len) released.locations ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span beforeMachine post ∧
      Nonempty (GeneralBorrowForestAccessData.Context released target primary extras) ∧
      released.indexOfTag targetNode.tag = some target ∧ released.nodes.data.size ≤ 4294967296 ∧
      GeneralBorrowFreshReleaseLoop.ActiveOn released target .Write offset (offset+len) := by
  obtain ⟨root,post,released,trace,frameEq,memoryEq,tracked,releaseEq,mutable,runtime⟩ := GeneralBorrowForestMixedLenCallReturnFull.executes options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    parent primary extras context covered tagPresent tagFresh nodeTags unheld slot fits
    well clean rangePositive owned allocationSize valid live uncached noClocks ghost shallow
    cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
    target targetNode targetPresent exprFree prefixPath exprOutside rootPath
  have resources := GeneralBorrowForestMixedSharedRestoredResources.prepare entry.allocation.extra tracker {} id exprTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits (UInt64.pos_iff_ne_zero.mp positive) well (by rw [allocationSize];exact bounds)
    clean owned target targetNode targetPresent rangePositive exprFree prefixPath exprOutside rootPath targetActive
  have actualTree : (GeneralBorrowForestMixedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
      |>.releaseProtector tracker.global.nextPointerTag (TypedBorrowSteps.registeredTracker tracker tracker.global.nextPointerTag).global.protectedTags).tree = released :=
    congrArg BorrowTree.ProtectorReleaseResult.tree releaseEq
  change Nonempty (GeneralBorrowForestAccessData.Context _ target primary extras) ∧ _ at resources
  rw [actualTree] at resources
  exact ⟨root,post,released,trace,frameEq,memoryEq,tracked,releaseEq,mutable,runtime,
    resources.1,resources.2.1,resources.2.2.1,resources.2.2.2.1⟩

end
end DuplicatePrefix.GeneralBorrowForestMixedLenCallReturnResources
