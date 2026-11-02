import duplicate_prefix.RootZeroCompleteState
import duplicate_prefix.GeneralBorrowForestMixedLenBeforeReturn
import duplicate_prefix.GeneralBorrowForestMixedSharedReleaseData
import duplicate_prefix.GeneralBorrowForestMixedLenReturn
namespace DuplicatePrefix.GeneralBorrowForestMixedLenCallReturnRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
structure RuntimeFacts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before after : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop where
  ghost : after.user.payload.ghost=false
  shallow : after.user.payload.validation=.Shallow
  race : after.dataRace=none
  addresses : after.user.addresses=before.user.addresses
  types : after.user.payload.payload.user.types=before.user.payload.payload.user.types
  extras : after.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
  backend : after.user.payload.payload.user.backend=.none
  unchecked : ((config options (remaining+1) span).terminators.getControl after.user).checkedArithmetic=false
  noGc : ((config options (remaining+1) span).terminators.getControl after.user).gcInterval=0
  fixed : after.threads.fixedScheduling=true
  active : ∃ thread, after.threads.activeThread?=some thread

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
    (writable : Nat → Bool) (well : entry.allocation.extra.locations.WellFormed)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) entry.allocation.extra.locations)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data entry.allocation.extra location tracker.global.protectedTags parent primary extras writable))
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
    (fixed : beforeMachine.threads.fixedScheduling = true) :
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
        (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data released location held.global.protectedTags
          (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
          (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)))
        offset (offset+len) released.locations ∧ RuntimeFacts options remaining span beforeMachine post := by
  let root := cachedCaller caller valid
  let childTree := GeneralBorrowForestMixedSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  obtain ⟨helper,atReturn,properties,facts,rootCache⟩ := GeneralBorrowForestMixedLenBeforeReturn.before_return_full_data options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    parent primary extras context covered tagPresent tagFresh nodeTags unheld slot fits writable well owned allocationSize valid live uncached noClocks ghost shallow
    cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
  rcases properties with ⟨prefixTrace,helperLocation,retval,helperTracked,helperRace,destination,continuation,varargs,
    memoryEq,heldEq,ghostEq,shallowEq,raceEq,addressesEq,typesEq,extrasEq⟩
  have data := GeneralBorrowForestMixedSharedReleaseData.prepare entry.allocation.extra tracker {} id exprTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits writable (UInt64.pos_iff_ne_zero.mp positive) well
    (by rw [allocationSize];exact bounds) clean owned
  obtain ⟨nextContext⟩ := data.1
  let inside : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra childTree}
  have found : atReturn.memory.live.find? (fun row => row.1 == id) = some (id,inside) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same beforeMachine.memory id entry childTree
  have nextFits : childTree.nodes.data.size ≤ 4294967296 := by
    let initialTree := entry.allocation.extra
    have mapBounds : offset.toNat+len.toNat ≤ initialTree.locations.size.bytes.toNat := by rw [allocationSize];exact bounds
    have sliceNonzero : len ≠ 0 := UInt64.pos_iff_ne_zero.mp positive
    let protections := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    have registration := GeneralBorrowForestMixedRegister.registered initialTree tracker.global ({} : FrameState) id
      tracker.global.nextPointerTag .StrongProtector parent primary extras writable tagFresh nodeTags unheld offset (offset+len) owned
    have good := GeneralBorrowForestMixedSlice.access initialTree protections exprTag parent primary extras (Size.ofBytes offset) (Size.ofBytes len)
      writable .VisitChildrenOfAccessed context tagPresent well fits offset (offset+len) registration.2.2.2 mapBounds (Nat.le_refl _) (Nat.le_refl _)
    let read := initialTree.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    have frame := GeneralBorrowFreshReadFrame.frame initialTree (.concrete exprTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    change read.tree = {initialTree with locations := read.tree.locations} at frame
    have nodes : read.tree.nodes = initialTree.nodes := by simpa only using congrArg BorrowTree.nodes frame
    have mapping : read.tree.tagMapping = initialTree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
    let depth := GeneralBorrowFreshReadFrame.depth_on initialTree read.tree nodes context.depth
    let nextSlot := GeneralBorrowFreshMetadataChildSlot.transport initialTree read.tree context.depth depth nodes mapping rfl parent slot
    have slotEq := GeneralBorrowFreshMetadataChildSlot.transport_index initialTree read.tree context.depth depth nodes mapping rfl parent slot
    have present : read.tree.nodeAt parent = some context.anchorNode := by
      change read.tree.nodes.get parent = _
      rw [nodes]
      exact context.anchorPresent
    have nextTag : read.tree.indexOfTag exprTag = some parent := by rw [frame];exact tagPresent
    have nextFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact tagFresh
    have nextChildren : GeneralBorrowGraph.ChildNodes read.tree := by rw [frame];exact context.children
    have nextCovered : GeneralBorrowGraph.RootsCover read.tree := by rw [frame];exact covered
    have nextBounds : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact mapBounds
    have readFits : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
    change (GeneralBorrowFreshMetadataChildSlot.result read.tree exprTag tracker.global.nextPointerTag true offset len).nodes.data.size ≤ _
    cases nextSlot with
    | append noFree aligned room =>
      let input : GeneralBorrowFreshMetadataChildShared.Input :=
        ⟨read.tree,depth,nextChildren,nextCovered,exprTag,tracker.global.nextPointerTag,parent,context.anchorNode,nextTag,present,nextFresh,
          noFree,aligned,room,true,offset,len,sliceNonzero,good.2.2.1,nextBounds⟩
      have size := (GeneralBorrowFreshMetadataChildShared.append input).size
      change (GeneralBorrowFreshMetadataChildShared.result input).nodes.size ≤ _
      rw [size]
      change read.tree.nodes.data.size+1 ≤ _
      omega
    | reuse index available bounded vacant slack =>
      let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
        ⟨read.tree,depth,nextChildren,nextCovered,exprTag,tracker.global.nextPointerTag,parent,context.anchorNode,nextTag,present,nextFresh,
          index,available,bounded,vacant,slack,true,offset,len,sliceNonzero,good.2.2.1,nextBounds⟩
      have size := (GeneralBorrowFreshMetadataChildSharedReuse.reuse input).size
      change (GeneralBorrowFreshMetadataChildSharedReuse.result input).nodes.size ≤ _
      rw [size]
      exact readFits
  have release := GeneralBorrowForestMixedReleaseFrame.release childTree held.global.protectedTags tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
    (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)
    offset (offset+len) rangePositive nextFits nextContext data.2.2.1 data.2.2.2.2 data.2.1
  have complete : childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags =
      ⟨(childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree,.Released⟩ := by
    cases eqn : childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags with
    | mk tree status => have done := release.1; rw [eqn] at done;cases done;rfl
  let releasedMemory := StackPopRelease.commitTree atReturn.memory id inside
    (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  have plan : StackPopRelease.Plan held.global.protectedTags borrowFrame.protectedTags.toList atReturn.memory releasedMemory :=
    StackPopRelease.Plan.live id tracker.global.nextPointerTag inside _ [] atReturn.memory _ found complete (.nil _)
  have valid0 : (0 : MIR.LocalId)<helper.locals.size := by rw [facts.size];decide
  have returnedLocal : helper.locals[0]'valid0 =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans retval)
  have immediate : ∀ slot ∈ helper.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
    apply PtrMetadataComplete.all_direct_three helper.locals facts.size
    · simp only [retval,Option.map_some,PtrMetadataComplete.isDirect]
    · simp only [facts.argument,Option.map_some,PtrMetadataComplete.isDirect]
    · have known := congrArg (Option.map PtrMetadataComplete.isDirect) facts.dead2
      simpa only [Option.map_map,Function.comp_def,Option.map_some,PtrMetadataComplete.isDirect] using known
  obtain ⟨returnThread,returnActive⟩ := facts.active
  have caller11 : (11 : MIR.LocalId)<root.locals.size := by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid
  have callerLive : root.locals[11].value = .live (.immediate .uninit) := by
    simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using live
  have callerCached : root.locals[11].layout=some RootCompilerFacts.usizeLayout := by simp [root,cachedCaller,LocalPlaces.cachePlaceLayout]
  have callerRace : root.extra.dataRace=none := noClocks
  have returned := LenReturn.step_with_plan options limits remaining span debugOff validityFuel validationEq frames root helper atReturn len
    facts.body helperLocation valid0 (congrArg LocalState.value returnedLocal) (congrArg LocalState.layout returnedLocal) helperRace
    11 caller11 callerLive callerCached callerRace destination 3 .Continue continuation immediate varargs held borrowFrame heldEq helperTracked
    releasedMemory plan returnThread returnActive facts.unchecked facts.noGc facts.fixed ghostEq shallowEq
  let released := (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  let finalRoot : CompilerFrameContext.ActualFrame :=
    {writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 len))) caller11 with location := .mir ⟨3,0⟩}
  let post := poppedMachine frames root helper
    (ActualPopPlan.released (accountedMachine options remaining span atReturn) releasedMemory held borrowFrame)
    (returnThread.topUserRelevantFrame.getD (frames.push root).size)
  have postMemory : post.memory = releasedMemory := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have postTracked : post.borrowTracker = some {held with global := held.global.endCall borrowFrame} := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have memoryFinal : releasedMemory = RetagEntry.updatedMemory beforeMachine.memory id entry released := by
    change RetagEntry.updatedMemory atReturn.memory id inside released = _
    rw [memoryEq]
    exact RetagEntry.updated_memory_twice beforeMachine.memory id entry childTree released
  have postGhost : post.user.payload.ghost=false := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_ghost];exact ghostEq
  have postShallow : post.user.payload.validation=.Shallow := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_validation];exact shallowEq
  have postFlags :
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic=false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval=0 := by
    simp only [post,popped_user,ActualPopPlan.released]
    exact ⟨(RootZeroCompleteState.tick_flags options remaining span atReturn).1.trans facts.unchecked,
      (RootZeroCompleteState.tick_flags options remaining span atReturn).2.trans facts.noGc⟩
  have postFixed : post.threads.fixedScheduling=true := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact facts.fixed
  have tickData : (RootZeroCompleteState.tick options remaining span atReturn).user.addresses=atReturn.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span atReturn).user.payload.payload.user.types=atReturn.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span atReturn).user.payload.payload.user.runtime.extras=atReturn.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span atReturn).user.payload.payload.user.backend=atReturn.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have postData : post.user.addresses=atReturn.user.addresses ∧
      post.user.payload.payload.user.types=atReturn.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras=atReturn.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend=atReturn.user.payload.payload.user.backend := by
    simpa only [post,popped_user,ActualPopPlan.released,RootZeroCompleteState.tick,accountedMachine] using tickData
  have runtime : RuntimeFacts options remaining span beforeMachine post := by
    refine ⟨postGhost,postShallow,?_,postData.1.trans addressesEq,postData.2.1.trans typesEq,
      postData.2.2.1.trans extrasEq,postData.2.2.2.trans facts.backend,postFlags.1,postFlags.2,postFixed,?_⟩
    · unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      split <;> exact raceEq
    · let releasedMachine := ActualPopPlan.released (accountedMachine options remaining span atReturn) releasedMemory held borrowFrame
      have known : releasedMachine.threads.activeThread?=some returnThread := returnActive
      unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      split
      · exact ⟨_,MetadataOutputFacts.relevance_active (frames.push root) helper releasedMachine returnThread known⟩
      · exact ⟨returnThread,known⟩
  exact ⟨finalRoot,post,released,SuccessfulTrace.append prefixTrace (.next returned (.refl _)),rfl,
    postMemory.trans memoryFinal,postTracked,complete,release.2.2,runtime⟩
end
end DuplicatePrefix.GeneralBorrowForestMixedLenCallReturnRuntime
