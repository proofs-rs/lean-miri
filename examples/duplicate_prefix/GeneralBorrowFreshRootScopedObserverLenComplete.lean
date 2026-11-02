import duplicate_prefix.GeneralBorrowFreshRootScopedSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowFreshRootScopedObserverSharedFnEntryResources
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryGraph
import duplicate_prefix.GeneralBorrowReadObserverPath
import duplicate_prefix.GeneralBorrowFreshRootScopedObserverReadRestore
import duplicate_prefix.GeneralBorrowActiveWithinRelease
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedObserverLenComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open GeneralBorrowForestMixedLenBeforeReturn
/-- Complete ACTUAL len helper call, from BEFORE its fresh tag allocation to
physical return, restoring the original mutable observer's full Positive and
activity on the exact post-memory. Every observer/graph/path/release fact after
initialization is derived internally from current raw inputs. -/
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input entry.allocation.extra tracker.global)
    (parentTagEq : input.parentTag = exprTag) (offsetEq : input.offset = offset) (lenEq : input.len = len)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
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

    (parentNode observerNode : TreeNode) (observer : UniIndex)
    (parentPresent : entry.allocation.extra.nodeAt input.parent = some parentNode)
    (edge : parentNode.parent = some observer) (parentHidden : parentNode.isExposed = false)
    (parentUnprotected : tracker.global.protectedTags.contains parentNode.tag = false)
    (observerPresent : entry.allocation.extra.nodeAt observer = some observerNode)
    (observerOwned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowObserverReadRange.Observer entry.allocation.extra tracker.global.protectedTags observer)
      offset (offset+len) entry.allocation.extra.locations)
    (observerActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra observer .Write offset (offset+len))
    (stepRoom : entry.allocation.extra.nodes.size+1 < 65536) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
    let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let released := (borrowedTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
    ∃ result post child,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent frames result post) ∧
      result = {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 len)))
        (by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location := .mir ⟨3,0⟩} ∧
      result.location = .mir ⟨3,0⟩ ∧
      post.memory = RetagEntry.updatedMemory beforeMachine.memory id entry released ∧
      post.borrowTracker = some {held with global := held.global.endCall borrowFrame} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released (held.global.endCall borrowFrame) ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive released (held.global.endCall borrowFrame).protectedTags
        child input.selected input.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released child .Write offset (offset+len) ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive released (held.global.endCall borrowFrame).protectedTags
        observer input.selected input.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released observer .Write offset (offset+len) ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = beforeMachine.user.addresses ∧
      post.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧
      (frames=#[] → ∃ thread,post.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0) := by
  let borrowedTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let released := (borrowedTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  have initialPath := GeneralBorrowReadObserverPath.parent entry.allocation.extra tracker.global runtime
    input.parent observer input.selected (some input.maximum) input.offset input.len input.positive.base parentNode parentPresent edge
  have initialObserver : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowObserverReadRange.Observer entry.allocation.extra tracker.global.protectedTags observer)
      input.offset (input.offset+input.len) entry.allocation.extra.locations := by
    simpa only [offsetEq,lenEq] using observerOwned
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra observer .Write
      input.offset (input.offset+input.len) := by simpa only [offsetEq,lenEq] using observerActivity
  have observerResources := GeneralBorrowFreshRootScopedObserverSharedFnEntryResources.resources entry.allocation.extra tracker {} id runtime input
    parentNode observerNode observer parentPresent edge parentHidden parentUnprotected observerPresent
    (initialPath default tracker.global.protectedTags) initialObserver initialActivity
  have usualResources := GeneralBorrowFreshRootScopedSharedFnEntryResources.resources entry.allocation.extra tracker {} id runtime input
  have graphResources := GeneralBorrowFreshRootScopedSharedFnEntryGraph.graph entry.allocation.extra tracker {} id runtime input
  have observerResourcesExact :
      DuplicatePrefixBorrowContract.RuntimeFacts borrowedTree held.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin borrowedTree observer .Write offset (offset+len) ∧
      ∃ child,borrowedTree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive borrowedTree held.global.protectedTags child input.selected input.maximum offset len) ∧
        GeneralRangeMapOrigins.OwnedOn
          (GeneralBorrowObserverReadRange.Observer borrowedTree
            (GeneralBorrowObserverReadRow.virtual held.global id tracker.global.nextPointerTag parentNode.tag) observer)
          offset (offset+len) borrowedTree.locations := by
    simpa only [borrowedTree,held,TypedBorrowSteps.registeredTracker,parentTagEq,offsetEq,lenEq] using observerResources
  obtain ⟨borrowedRuntime,borrowedObserverActivity,observerChild,observerLookup,_,borrowedObserver⟩ := observerResourcesExact
  have usualResourcesExact :
      DuplicatePrefixBorrowContract.RuntimeFacts borrowedTree held.global ∧
      borrowedTree.locations.size = entry.allocation.extra.locations.size ∧
      borrowedTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 ∧
      borrowedTree.roots = entry.allocation.extra.roots ∧
      held.global.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector ∧
      GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag ∧
      ∃ child,borrowedTree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive borrowedTree held.global.protectedTags input.parent input.selected input.maximum offset len) ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive borrowedTree held.global.protectedTags child input.selected input.maximum offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin borrowedTree child .Read offset (offset+len) := by
    simpa only [borrowedTree,held,TypedBorrowSteps.registeredTracker,parentTagEq,offsetEq,lenEq] using usualResources
  obtain ⟨_,_,growth,roots,_,_,child,lookup,_,⟨childPositive⟩,childActivity⟩ := usualResourcesExact
  have sameObserverChild : observerChild = child := Option.some.inj (observerLookup.symm.trans lookup)
  have graphExact :
      ∃ child,borrowedTree.indexOfTag tracker.global.nextPointerTag = some child ∧
        (∃ node,borrowedTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧
          node.parent = some input.parent ∧ node.isExposed = false) ∧
        (∀ query oldNode,entry.allocation.extra.nodeAt query = some oldNode →
          ∃ next,borrowedTree.nodeAt query = some next ∧ next.tag = oldNode.tag ∧
            next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed) := by
    simpa only [borrowedTree,parentTagEq,offsetEq,lenEq] using graphResources
  obtain ⟨graphChild,graphLookup,⟨childNode,childPresent,childTag,childParent,childHidden⟩,oldNodes⟩ := graphExact
  have sameGraphChild : graphChild = child := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphChild
  obtain ⟨temporaryNode,temporaryPresent,temporaryTag,temporaryParent,temporaryHidden⟩ := oldNodes input.parent parentNode parentPresent
  obtain ⟨currentObserver,observerPresentAfter,_,_,_⟩ := oldNodes observer observerNode observerPresent
  have temporaryEdge : temporaryNode.parent = some observer := temporaryParent.trans edge
  have temporaryHiddenAfter : temporaryNode.isExposed = false := temporaryHidden.trans parentHidden
  obtain ⟨_,_,_,_,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} id input.tagRoom runtime
  have parentDifferent : parentNode.tag ≠ tracker.global.nextPointerTag := nodeFresh (input.parent,parentNode)
    (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get entry.allocation.extra.nodes input.parent parentNode).mpr parentPresent))
  have temporaryUnprotected : held.global.protectedTags.contains temporaryNode.tag = false := by
    rw [temporaryTag]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains parentNode.tag = false
    rw [ProtectorInsertion.contains_other _ _ _ _ parentDifferent]
    exact parentUnprotected
  have borrowedObserverExact : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowObserverReadRange.Observer borrowedTree
        (GeneralBorrowObserverReadRow.virtual held.global id childNode.tag temporaryNode.tag) observer)
      offset (offset+len) borrowedTree.locations := by
    simpa only [childTag,temporaryTag] using borrowedObserver
  have observerPath := GeneralBorrowReadObserverPath.two_parents borrowedTree held.global borrowedRuntime
    child input.parent observer input.selected (some input.maximum) offset len childPositive.base childNode temporaryNode
    childPresent childParent temporaryPresent temporaryEdge
  have distinct : borrowedTree.roots.toList.Nodup := by rw [roots];exact input.distinct
  have short : borrowedTree.nodes.size < 65536 := Nat.lt_of_le_of_lt growth stepRoom
  have tagged : borrowedTree.indexOfTag childNode.tag = some child := by rw [childTag];exact lookup
  obtain ⟨_,_,_,restored,_,_,_⟩ := GeneralBorrowFreshRootScopedObserverReadRestore.release_end_call borrowedTree held.global borrowedRuntime
    id child input.selected input.parent observer input.maximum childNode temporaryNode currentObserver
    childPresent childParent temporaryPresent temporaryEdge observerPresentAfter childHidden temporaryHiddenAfter temporaryUnprotected
    (observerPath default _) offset len childPositive borrowedObserverExact tagged distinct short childActivity
  have observerActivityAfter := GeneralBorrowActiveWithinRelease.release borrowedTree held.global.protectedTags
    tracker.global.nextPointerTag child observer childNode lookup childPresent childHidden offset (offset+len)
    (GeneralBorrowFreshActiveWithin.to_write borrowedTree child offset (offset+len) childActivity) borrowedObserverActivity
  obtain ⟨result,post,returnedChild,trace,resultEq,locationEq,memoryEq,trackerEq,postRuntime,postPositive,postActivity,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowFreshRootScopedSharedLenCompleteFrame.complete
      options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh runtime input
      parentTagEq offsetEq lenEq bounds allocationSize valid live uncached noClocks ghost shallow cachedAddress present race
      thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source
      sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed stepRoom
  refine ⟨result,post,returnedChild,trace,resultEq,locationEq,memoryEq,trackerEq,postRuntime,postPositive,postActivity,?_,
    observerActivityAfter,ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩
  simpa only [childTag] using restored
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedObserverLenComplete
