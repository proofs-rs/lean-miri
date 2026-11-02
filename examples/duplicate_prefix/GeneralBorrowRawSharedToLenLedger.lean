import duplicate_prefix.GeneralBorrowSharedLenHelperGraph
import duplicate_prefix.GeneralBorrowSharedLenReleasedGraph
import duplicate_prefix.GeneralBorrowRawSharedOldGraph
import duplicate_prefix.GeneralBorrowSharedFnEntryGlobalReturn
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
import duplicate_prefix.GeneralBorrowObserverLenComplete
import duplicate_prefix.GeneralBorrowRawSharedStatementBoth
import duplicate_prefix.GeneralBorrowRawSharedStatement
import duplicate_prefix.GeneralBorrowRawSharedLenCompleteFrame
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
import duplicate_prefix.LenCallResultFrame
namespace DuplicatePrefix.GeneralBorrowRawSharedToLenLedger
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem fn3 {A B C D : Type} (f : A → B → C → D)
    (a1 a2 : A) (b1 b2 : B) (c1 c2 : C)
    (first : a1 = a2) (second : b1 = b2) (third : c1 = c2) : f a1 b1 c1 = f a2 b2 c2 := by
  cases first
  cases second
  cases third
  rfl

structure Graph (before after : BorrowTree) (selected : Miri.TreeBorrows.UniIndex)
    (beforeTracker afterTracker : MachineHooks.BorrowState) : Prop where
  capacity : after.locations.size = before.locations.size
  roots : after.roots = before.roots
  growth : after.nodes.size ≤ before.nodes.size+2
  short : after.nodes.size < 65536
  distinct : after.roots.toList.Nodup
  order : ∀ valid : 0 < after.roots.size, selected ≠ after.roots[0]'valid →
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder after
  oldNodes : ∀ query oldNode, before.nodeAt query = some oldNode →
    ∃ next, after.nodeAt query = some next ∧ next.tag = oldNode.tag ∧
      next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed ∧ after.indexOfTag oldNode.tag = some query
  protections : afterTracker.global.protectedTags = beforeTracker.global.protectedTags
  tagCounter : afterTracker.global.nextPointerTag.value.toNat = beforeTracker.global.nextPointerTag.value.toNat+2

theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (shortRoom : entry.allocation.extra.nodes.size+2 < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (rootCall : frames = #[]) (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (source : PreparedContracts.SourceComparator)
    (valid11 : 11 < frame.locals.size) (lenLive : frame.locals[11].value = .live (.immediate .uninit))
    (lenUncached : frame.locals[11].layout = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (both : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum offset len)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra raw.parent .Write offset (offset+len)) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
    ∃ (result : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (finalTree : BorrowTree) (held : MachineHooks.BorrowState) (child : UniIndex),
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames result post) ∧
      result = LenCallResultFrame.resultFrame caller (by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using valid11) len ∧
      post.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧ post.borrowTracker = some held ∧ held.retagMode = tracker.retagMode ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      Nonempty (GeneralBorrowReadRowRange.Positive finalTree held.global.protectedTags child raw.selected raw.maximum offset len) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree raw.parent .Write offset (offset+len) ∧
      Graph entry.allocation.extra finalTree raw.selected tracker held ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧ post.dataRace = none ∧
      post.user.addresses = machine.user.addresses ∧ post.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend = .none ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧ ∃ nextThread, post.threads.activeThread? = some nextThread ∧ nextThread.topUserRelevantFrame = some 0 := by
  subst frames
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  let exprTree := (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag
    tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  let exprTracker := ReferenceBorrowDriver.allocatedTracker tracker fresh
  let exprMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with memory := RetagEntry.updatedMemory machine.memory id entry exprTree}
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let caller := GeneralBorrowForestSharedPreLenFrame.after frame validDest value
  obtain ⟨statement,exprRuntime,exprCapacity,nextInput,nextTag,nextSelected,nextMaximum,nextOffset,nextLen,
    ⟨parentBoth⟩,parentActivity,temporary,tempNode,observerNode,tempLookup,tempPresent,tempTag,tempParent,tempHidden,tempFree,observerPresent⟩ :=
    GeneralBorrowRawSharedStatementBoth.step_resources options limits remaining span preciseOff implicitOff debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits #[] frame machine
      sourceBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
      validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
      (by omega) nodeRoom tagRoom both activity
  have temporaryEq : temporary = nextInput.parent := by
    have lookup : exprTree.indexOfTag tracker.global.nextPointerTag = some nextInput.parent := (congrArg (fun tag => exprTree.indexOfTag tag) nextTag.symm).trans nextInput.tagged
    exact Option.some.inj (tempLookup.symm.trans lookup)
  subst temporary
  have observerOwned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowObserverReadRange.Observer exprTree exprTracker.global.protectedTags raw.parent)
      offset (offset+len) exprTree.locations := by
    intro position valid nonempty before after
    obtain ⟨row⟩ := parentBoth.rows position valid nonempty before after
    exact row.normal raw.parent rfl
  have exprStep : ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame machine) = (Storage.withCurrent #[] caller exprMachine,.ok true) := by
    simpa only [caller,GeneralBorrowForestSharedPreLenFrame.after,exprMachine,exprTree,value,RootReferenceFacts.destination,
      RootReferenceFacts.location,RootReferenceInfo.layout,ite_true] using statement
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra exprTree}
  have bufferPresent : exprMachine.memory.live.find? (fun row => row.1 == id) = some (id,buffer) :=
    StackPopRelease.lookup_commit_same machine.memory id entry exprTree
  have callerValid : 11 < caller.locals.size := by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using valid11
  have callerLive : caller.locals[11].value = .live (.immediate .uninit) := by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenLive
  have callerUncached : caller.locals[11].layout = none := by
    simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set] using lenUncached
  have callerSourceValid : 12 < caller.locals.size := by simpa [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination] using validDest
  have callerSource : caller.locals[12].value = .live (.immediate value) := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,validDest]
  have callerCached : caller.locals[12].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [caller,GeneralBorrowForestSharedPreLenFrame.after,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,validDest]
  let callMachine := PtrMetadataReturn.accountedMachine options remaining span exprMachine
  have callGhost : callMachine.user.payload.ghost = false := (PtrMetadataReturn.accounted_ghost options remaining span exprMachine).trans ghost
  have callShallow : callMachine.user.payload.validation = .Shallow := (PtrMetadataReturn.accounted_validation options remaining span exprMachine).trans shallow
  have callAddresses : callMachine.user.addresses = machine.user.addresses := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have callCached : callMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [callAddresses];exact cachedAddress
  have callBackend : callMachine.user.payload.payload.user.backend = .none := by
    unfold callMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  let helperCaller := LenUncachedFrontend.cachedCaller caller callerValid
  let destination := (LocalPlaces.localRuntimePlace 0 helperCaller 11 RootCompilerFacts.usizeLayout).stackView
  let state := Storage.withCurrent #[] helperCaller callMachine
  have callActive : callMachine.threads.activeThread? = some thread := active
  have callTop : FrameRelevance.top (LenPush.pushed options.userRelevantCrates state destination).stack thread.topUserRelevantFrame = some 0 := by
    simp [FrameRelevance.top,topZero]
  have current : (LenPush.pushed options.userRelevantCrates state destination).stack.frames[0]? = some helperCaller := by
    simp [LenPush.pushed,state,Storage.withCurrent]
  have pushMetadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination helperCaller)).metadata = PreparedReflection.actual.runtime := by
    change (LenPushFacts.posted options remaining span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.metadata = _
    rw [LenPushFacts.types_eq]
    exact metadata
  have pushNotConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates state destination helperCaller)).entries.any (·.value.ty == 4) = false := by
    change (LenPushFacts.posted options remaining span #[] helperCaller exprMachine helperCaller).user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [LenPushFacts.types_eq]
    exact notConstructed
  have shortNext : exprTree.nodes.size+1 < 65536 := by
    obtain ⟨_,_,_,growth,_,_,_⟩ := GeneralBorrowRawSharedResources.resources entry.allocation.extra tracker.global runtime raw
    have h : exprTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 := by simpa only [exprTree,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,rawTag,rawOffset,rawLen] using growth
    omega
  have physicalBounds : offset.toNat+len.toNat ≤ buffer.allocation.byteSize.bytes.toNat := by
    have h := raw.positive.bounds
    rw [rawOffset,rawLen,capacity] at h
    exact h
  obtain ⟨result,post,child,lenTrace,resultEq,resultLocation,memoryAfter,trackerAfter,runtimeAfter,positiveAfter,activityAfter,originalBoth,originalActivity,
    ghostAfter,shallowAfter,raceAfter,addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,topAfter⟩ :=
    GeneralBorrowObserverLenComplete.complete options limits remaining budget dispatch span ctx debugOff cmp
      dynamicFuel validityFuel fuelEq validationFuel id buffer base offset len tracker.global.nextPointerTag positive nonzero signedFits
      #[] caller callMachine exprTracker rfl defaultMode nextInput.tagRoom exprRuntime nextInput nextTag nextOffset nextLen physicalBounds
      (exprCapacity.trans capacity) callerValid callerLive callerUncached noClocks callGhost callShallow callCached bufferPresent race
      thread 0 helperCaller callActive callTop current pushMetadata pushNotConstructed sourceBody identity callee rfl source
      callerSourceValid callerSource callerCached callBackend exprMachine rfl unchecked noGc fixed
      tempNode observerNode raw.parent tempPresent tempParent tempHidden tempFree observerPresent observerOwned parentActivity shortNext
  let borrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree exprTree exprTracker nextInput.parentTag nextInput.offset nextInput.len
  let helperHeld := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker exprTracker nextInput.tagRoom) exprTracker.global.nextPointerTag
  let borrowFrame := ({} : FrameState).addProtector id exprTracker.global.nextPointerTag
  let released := (borrowed.releaseProtector exprTracker.global.nextPointerTag helperHeld.global.protectedTags).tree
  let finalTracker := {helperHeld with global := helperHeld.global.endCall borrowFrame}
  let canonicalBorrowed := GeneralBorrowRawSharedFnEntryArgument.finalTree exprTree exprTracker tracker.global.nextPointerTag offset len
  let canonicalReleased := (canonicalBorrowed.releaseProtector exprTracker.global.nextPointerTag helperHeld.global.protectedTags).tree
  have borrowedEq : borrowed = canonicalBorrowed :=
    @fn3 BorTag UInt64 UInt64 BorrowTree (GeneralBorrowRawSharedFnEntryArgument.finalTree exprTree exprTracker)
      nextInput.parentTag tracker.global.nextPointerTag nextInput.offset offset nextInput.len len nextTag nextOffset nextLen
  have releasedEq : released = canonicalReleased := congrArg (fun tree => (tree.releaseProtector exprTracker.global.nextPointerTag helperHeld.global.protectedTags).tree) borrowedEq
  let exprRaw := (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags raw.parentTag tracker.global.nextPointerTag raw.offset raw.len .VisitChildrenOfAccessed).tree
  have exprEq : exprRaw = exprTree :=
    @fn3 BorTag UInt64 UInt64 BorrowTree
      (fun tag offset len => (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree)
      raw.parentTag parentTag raw.offset offset raw.len len rawTag rawOffset rawLen
  obtain ⟨_,_,exprCap,exprGrowth,exprRoots,_,_⟩ := GeneralBorrowRawSharedResources.resources entry.allocation.extra tracker.global runtime raw
  have exprCapExact : exprTree.locations.size = entry.allocation.extra.locations.size := by
    simpa only [exprTree,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,rawTag,rawOffset,rawLen] using exprCap
  have exprRootsExact : exprTree.roots = entry.allocation.extra.roots := by
    simpa only [exprTree,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,rawTag,rawOffset,rawLen] using exprRoots
  have exprGrowthExact : exprTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 := by
    simpa only [exprTree,GeneralBorrowRawSharedExpression.child,GeneralBorrowRawSharedExpression.read,rawTag,rawOffset,rawLen] using exprGrowth
  have exprOldRaw : ∀ query oldNode, entry.allocation.extra.nodeAt query = some oldNode →
      ∃ next,exprRaw.nodeAt query = some next ∧ next.tag=oldNode.tag ∧ next.parent=oldNode.parent ∧ next.isExposed=oldNode.isExposed :=
    GeneralBorrowRawSharedOldGraph.frame entry.allocation.extra tracker.global runtime raw
  have exprOld : ∀ query oldNode, entry.allocation.extra.nodeAt query = some oldNode →
      ∃ next,exprTree.nodeAt query = some next ∧ next.tag=oldNode.tag ∧ next.parent=oldNode.parent ∧ next.isExposed=oldNode.isExposed := by
    rw [←exprEq]
    exact exprOldRaw
  let named := GeneralBorrowSharedLenHelperGraph.releasedTree exprTree exprTracker nextInput
  let ended := GeneralBorrowSharedLenHelperGraph.endedGlobal exprTracker id nextInput.tagRoom
  have helperGraph := GeneralBorrowSharedLenHelperGraph.package exprTree exprTracker {} id exprRuntime nextInput shortNext
  have namedEq : named = released := GeneralBorrowSharedLenHelperGraph.releasedTree_eq exprTree exprTracker nextInput
  have physicalEq : named = canonicalReleased := namedEq.trans releasedEq
  have globalEq : ended = finalTracker.global := GeneralBorrowSharedLenHelperGraph.endedGlobal_eq exprTracker id nextInput.tagRoom
  have table : finalTracker.global.protectedTags = tracker.global.protectedTags :=
    (congrArg (fun global : Miri.TreeBorrows.GlobalState => global.protectedTags) globalEq.symm).trans helperGraph.table
  have tagCounter : finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 := by
    have second := (congrArg (fun global : Miri.TreeBorrows.GlobalState => global.nextPointerTag.value.toNat) globalEq.symm).trans helperGraph.counter
    have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    change exprTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 at first
    omega
  have graphNamed : Graph entry.allocation.extra named raw.selected tracker finalTracker := by
    refine ⟨helperGraph.capacity.trans exprCapExact,helperGraph.roots.trans exprRootsExact,?_,
      helperGraph.short,helperGraph.distinct,?_,?_,table,tagCounter⟩
    · have growth : named.nodes.size ≤ exprTree.nodes.size+1 := helperGraph.growth
      exact Nat.le_trans growth (Nat.add_le_add_right exprGrowthExact 1)
    · simpa only [nextSelected] using helperGraph.order
    · intro query oldNode present
      obtain ⟨middle,middlePresent,middleTag,middleParent,middleHidden⟩ := exprOld query oldNode present
      obtain ⟨next,found,tag,parent,hidden⟩ := helperGraph.oldNodes query middle middlePresent
      have lookup := helperGraph.oldTags query middle middlePresent
      have oldLookup : named.indexOfTag oldNode.tag = some query :=
        (congrArg (fun tag => named.indexOfTag tag) middleTag.symm).trans lookup
      exact ⟨next,found,tag.trans middleTag,parent.trans middleParent,hidden.trans middleHidden,oldLookup⟩
  have graph : Graph entry.allocation.extra canonicalReleased raw.selected tracker finalTracker :=
    Eq.mp (congrArg (fun tree => Graph entry.allocation.extra tree raw.selected tracker finalTracker) physicalEq) graphNamed
  refine ⟨result,post,_,_,child,SuccessfulTrace.Trace.next exprStep lenTrace,?_,?_,trackerAfter,rfl,runtimeAfter,?_,?_,originalActivity,graph,ghostAfter,shallowAfter,raceAfter,
    addresses,types,extras,backendAfter,uncheckedAfter,noGcAfter,fixedAfter,?_⟩
  · simpa only [LenCallResultFrame.resultFrame,ActualLocalCopy.written,LenUncachedFrontend.cachedCaller,PtrMetadataExecution.writeFrame] using resultEq
  · rw [show exprMachine.memory = RetagEntry.updatedMemory machine.memory id entry exprTree from rfl] at memoryAfter
    exact memoryAfter.trans (RetagEntry.updated_memory_twice machine.memory id entry exprTree _)
  · simpa only [nextSelected,nextMaximum] using positiveAfter
  · simpa only [nextSelected,nextMaximum] using originalBoth
  · exact topAfter rfl
end
end DuplicatePrefix.GeneralBorrowRawSharedToLenLedger
