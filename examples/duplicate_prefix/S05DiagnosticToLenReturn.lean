import duplicate_prefix.S05DiagnosticSharedStep
import duplicate_prefix.PushThread
import duplicate_prefix.S05DiagnosticLenBody
import duplicate_prefix.S05DiagnosticLenReturn
namespace DuplicatePrefix.S05DiagnosticToLenReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open RootFrameData EmptyRootArguments PositiveRootArguments S05DiagnosticFnEntryScope
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open GeneralBorrowForestMixedLenBeforeReturn
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Output equations for the actual len Return, retaining its concrete machine construction. -/
def Post (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) (valid : 11 < caller.locals.size)
    (base offset : UInt64) (exprTag : BorTag) (result : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) : Prop :=
  let root := cachedCaller caller valid
  let tree := S05DiagnosticLenInstall.finalTree entry.allocation.extra tracker exprTag offset 2
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
  let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  ∃ helper middle thread,
    result = {PtrMetadataExecution.writeFrame root 11 (.scalar (.fromScalarInt (.ofUInt64 2))) (by simpa [root,cachedCaller,LocalPlaces.cachePlaceLayout] using valid) with location := .mir ⟨3,0⟩} ∧
    middle.memory = RetagEntry.updatedMemory before.memory id entry tree ∧ middle.borrowTracker = some held ∧
    middle.user.addresses = before.user.addresses ∧ middle.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
    middle.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras ∧
    middle.user.payload.ghost = false ∧ middle.user.payload.validation = .Shallow ∧ middle.dataRace = none ∧
    GeneralBorrowForestMixedLenBeforeReturn.ReturnFacts options remaining span helper middle 2
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 2 SharedReferenceMetadata.sharedLayout).imm ∧
    middle.threads.activeThread? = some thread ∧
    post = PtrMetadataReturn.poppedMachine frames root helper (ActualPopPlan.released
      (PtrMetadataReturn.accountedMachine options remaining span middle)
      (StackPopRelease.commitTree middle.memory id {entry with allocation := entry.allocation.setExtra tree} S05DiagnosticLenRelease.released)
      held owned) (thread.topUserRelevantFrame.getD (frames.push root).size) ∧
    post.memory = RetagEntry.updatedMemory before.memory id entry S05DiagnosticLenRelease.released ∧
    post.borrowTracker = some {held with global := held.global.endCall owned}
/-- Lower physical composition from the actual shared statement's caller site through
len and its Return. This theorem does not construct the original root call. -/
theorem from_shared_state
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
    (treeEq : entry.allocation.extra = S05DiagnosticLenRead.tree)
    (parentEq : exprTag = S05DiagnosticFnEntryRead.tag 10)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 11)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (offsetEq : offset = 0) (lenEq : len = 2)
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
 :
    ∃ (root : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent frames caller beforeMachine) (Storage.withCurrent frames root post) ∧
      root.location = .mir ⟨3,0⟩ ∧
      Post options remaining span frames caller beforeMachine id entry tracker fresh valid base offset exprTag root post := by
  subst len
  let root := cachedCaller caller valid
  let borrowedTree := S05DiagnosticLenInstall.finalTree entry.allocation.extra tracker exprTag offset 2
  obtain ⟨helper,finalMachine,data,facts,cache⟩ := S05DiagnosticLenBody.before_return
    options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset 2 exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh
    treeEq parentEq nextEq protectedEq offsetEq rfl bounds allocationSize valid live uncached noClocks ghost shallow
    cachedAddress present race thread index current active top presentFrame metadata notConstructed
    sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  obtain ⟨trace,location,retval,frameTracked,helperRace,destination,continuation,varargs,memoryEq,tracked,
    finalGhost,finalShallow,finalRace,addresses,types,extras⟩ := data
  have rootValid : 11 < root.locals.size := by simpa only [root,cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using valid
  have rootLive : root.locals[11].value = .live (.immediate .uninit) := by
    simpa only [root,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set,ite_true] using live
  have rootCached : root.locals[11].layout = some RootCompilerFacts.usizeLayout := by
    simp only [root,cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set,ite_true]
  have childEq : borrowedTree = (S05DiagnosticLenRead.afterRead.newChild Size.ZERO
      (.concrete (S05DiagnosticFnEntryRead.tag 10)) (S05DiagnosticFnEntryRead.tag 11)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree := by
    unfold borrowedTree S05DiagnosticLenInstall.finalTree
    simp only [treeEq,parentEq,nextEq,offsetEq,TypedBorrowSteps.registeredGlobal,protectedEq]
    change ((S05DiagnosticLenRead.tree.performBorrowAccessRange (.concrete (S05DiagnosticFnEntryRead.tag 10))
      Size.ZERO (Size.ofBytes 2) .Read S05DiagnosticLenRead.protections .VisitChildrenOfAccessed).tree.newChild
      Size.ZERO (.concrete (S05DiagnosticFnEntryRead.tag 10)) (S05DiagnosticFnEntryRead.tag 11) _ .Frozen true).tree = _
    rw [S05DiagnosticLenRead.read.2]
  have protections : (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh)
      tracker.global.nextPointerTag).global.protectedTags = S05DiagnosticLenRelease.protections := by
    change tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector = _
    rw [protectedEq,nextEq]
    rfl
  obtain ⟨returnThread,result,post,returnActive,step,resultEq,postMemory,postTracker,postEq⟩ := S05DiagnosticLenReturn.step_state
    options limits remaining span debugOff validityFuel validationEq frames root helper finalMachine
    _ facts location retval helperRace destination continuation varargs rootValid rootLive rootCached noClocks
    id entry borrowedTree beforeMachine.memory memoryEq
    (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)
    (({} : FrameState).addProtector id tracker.global.nextPointerTag) tracked frameTracked
    (by simp only [FrameState.addProtector,nextEq];rfl) childEq protections finalGhost finalShallow
  refine ⟨result,post,SuccessfulTrace.append trace (.next step (.refl _)),?_,helper,finalMachine,returnThread,
    resultEq,memoryEq,tracked,addresses,types,extras,finalGhost,finalShallow,finalRace,facts,returnActive,postEq,postMemory,postTracker⟩
  rw [resultEq]
/-- The two-byte physical diagnostic's original actual call through len Return.
The explicit physical size fixes this fixture; this is not an all-valid-input or whole-call NoUB theorem. -/
theorem from_call
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : entry.allocation.extra = S05DiagnosticFnEntryRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 6)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 8)
    (protectedEq : tracker.global.protectedTags = ({} : ProtectedTags))
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (source : PreparedContracts.SourceComparator)
    (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true)
    (physicalSize : entry.allocation.byteSize = Size.ofBytes 2)
 :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
    let entered : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}
    let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entered with allocation := entered.allocation.setExtra (S05DiagnosticSharedExpression.child entered.allocation.extra S05DiagnosticSharedRead.protections (S05DiagnosticFnEntryRead.tag 8) (S05DiagnosticFnEntryRead.tag 10) 0 2 .VisitChildrenOfAccessed).tree}
    ∃ (frame result : CompilerFrameContext.ActualFrame) (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second 1)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
          .ok () (Storage.withCurrent #[] frame machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result post) ∧ result.location = .mir ⟨3,0⟩ ∧
      ∃ (caller : CompilerFrameContext.ActualFrame) (shared : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (sharedTracker : MachineHooks.BorrowState) (valid : 11 < caller.locals.size)
        (postFresh : sharedTracker.global.nextPointerTag.value < 18446744073709551615),
        Post options remaining span #[] caller shared id sourceEntry sharedTracker postFresh valid base 0 (S05DiagnosticFnEntryRead.tag 10) result post ∧
        shared.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
        shared.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
        sharedTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 11 ∧ sharedTracker.retagMode = .Default ∧
        sharedTracker.global.protectedTags = S05DiagnosticSharedRead.protections ∧
        ∃ (site : CompilerFrameContext.ActualFrame) (siteShape : GenericFunctionEntryPrefix.Shape frame site 1),
          caller = CopyHelperSteps.advance (ActualLocalCopy.written site 12 (RootReferenceInfo.layout true)
            (by rw [siteShape.size];decide) (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 10)) (Size.ofBytes base)) 2 (RootReferenceInfo.layout true)).imm) ⟨2,11⟩ ∧
          frame = PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race)
            (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
            1 {} id tracker.global.nextPointerTag slotId (TypedRetagGeneric.protectedGlobal tracker.global fresh).nextPointerTag := by
  dsimp only
  obtain ⟨frame,caller,initial,shared,actual,trace,located,body,identity,callee,size,clocks,sourceSlot,destSlot,
    presentShared,cached,types,raceShared,ghostShared,shallowShared,backend,threads,uncheckedShared,noGcShared,fixedShared,
    sharedTracker,tracked,defaultMode,next11,protections,frameFacts⟩ := S05DiagnosticSharedStep.executes
    options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base nonzero
    entry bounds before ghost shallow cachedAddress present enabled fresh tree parentEq nextEq protectedEq race metadata notConstructed
    retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate
    slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
    source mode unchecked noGc fixed
  let entered : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}
  let sharedEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entered with allocation := entered.allocation.setExtra (S05DiagnosticSharedExpression.child entered.allocation.extra S05DiagnosticSharedRead.protections
      (S05DiagnosticFnEntryRead.tag 8) (S05DiagnosticFnEntryRead.tag 10) 0 2 .VisitChildrenOfAccessed).tree}
  have enteredTree : entered.allocation.extra = S05DiagnosticSharedRead.tree := by
    change S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2 = _
    rw [tree,parentEq]
    exact S05DiagnosticSharedRead.finalTree_eq tracker nextEq protectedEq
  have sharedTree : sharedEntry.allocation.extra = S05DiagnosticLenRead.tree := by
    change (S05DiagnosticSharedExpression.child entered.allocation.extra _ _ _ _ _ _).tree = _
    rw [enteredTree]
    unfold S05DiagnosticSharedExpression.child S05DiagnosticSharedExpression.read
    change ((S05DiagnosticSharedRead.tree.performBorrowAccessRange (.concrete (S05DiagnosticFnEntryRead.tag 8))
      Size.ZERO (Size.ofBytes 2) .Read S05DiagnosticSharedRead.protections .VisitChildrenOfAccessed).tree.newChild
      Size.ZERO (.concrete (S05DiagnosticFnEntryRead.tag 8)) (S05DiagnosticFnEntryRead.tag 10) _ .Frozen false).tree = _
    rw [S05DiagnosticSharedRead.read.2]
    exact S05DiagnosticLenRead.shared_tree
  let accounted := PtrMetadataReturn.accountedMachine options remaining span shared
  have valid11 : 11 < caller.locals.size := by rw [size];decide
  have valid12 : 12 < caller.locals.size := by rw [size];decide
  have cell11 := Option.some.inj ((Array.getElem?_eq_getElem valid11).symm.trans destSlot)
  have cell12 := Option.some.inj ((Array.getElem?_eq_getElem valid12).symm.trans sourceSlot)
  let root := cachedCaller caller valid11
  let current := root
  let activeThread := {thread with topUserRelevantFrame := some 0}
  have activeShared : shared.threads.activeThread? = some activeThread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have activeAccounted : accounted.threads.activeThread? = some activeThread := activeShared
  have top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent #[] root accounted)
      (LocalPlaces.localRuntimePlace 0 root 11 RootCompilerFacts.usizeLayout).stackView).stack activeThread.topUserRelevantFrame = some 0 := by
    rfl
  have framePresent : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent #[] root accounted)
      (LocalPlaces.localRuntimePlace 0 root 11 RootCompilerFacts.usizeLayout).stackView).stack.frames[0]? = some current := by rfl
  have queryTypes : EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates
      (Storage.withCurrent #[] root accounted) (LocalPlaces.localRuntimePlace 0 root 11 RootCompilerFacts.usizeLayout).stackView current) =
      before.user.payload.payload.user.types := by
    change (LenPushFacts.posted options remaining span #[] root shared current).user.payload.payload.user.types = _
    exact (LenPushFacts.types_eq options remaining span #[] root shared current).trans types
  have sharedFresh : sharedTracker.global.nextPointerTag.value < 18446744073709551615 := by rw [next11];decide
  obtain ⟨result,post,suffix,location,postFacts⟩ := from_shared_state options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id sharedEntry base 0 2 (S05DiagnosticFnEntryRead.tag 10)
    (by decide) (by simpa only [UInt64.add_zero] using nonzero) (by decide) #[] caller accounted sharedTracker tracked defaultMode
    sharedFresh sharedTree rfl next11 protections rfl rfl
    (by change (0 : Nat)+2 ≤ entry.allocation.byteSize.bytes.toNat; omega)
    (by rw [sharedTree];change Size.ofBytes 2 = entry.allocation.byteSize;exact physicalSize.symm)
    valid11 (by rw [cell11]) (by rw [cell11]) clocks
    ((PtrMetadataReturn.accounted_ghost options remaining span shared).trans ghostShared)
    ((PtrMetadataReturn.accounted_validation options remaining span shared).trans shallowShared)
    (by unfold accounted PtrMetadataReturn.accountedMachine SourceControl.accounted;rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators];exact cached)
    presentShared raceShared
    activeThread 0 current activeAccounted top framePresent
    (by simpa only [root,current,Array.size_empty] using (congrArg (fun t => t.metadata) queryTypes).trans metadata)
    (by simpa only [root,current,Array.size_empty] using (congrArg (fun t => t.entries.any (·.value.ty == 4)) queryTypes).trans notConstructed) body identity callee located source valid12
    (by simpa only [UInt64.add_zero,RootReferenceInfo.layout,↓reduceIte] using congrArg (fun c => c.value) cell12)
    (by exact congrArg (fun c => c.layout) cell12) (by unfold accounted PtrMetadataReturn.accountedMachine SourceControl.accounted;rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators];exact backend) shared rfl uncheckedShared noGcShared fixedShared
  exact ⟨frame,result,initial,post,actual,SuccessfulTrace.append trace suffix,location,
    caller,shared,sharedTracker,valid11,sharedFresh,postFacts,cached,types,next11,defaultMode,protections,frameFacts⟩
end
end DuplicatePrefix.S05DiagnosticToLenReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticToLenReturn." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic len composition dependency {dependency}"
