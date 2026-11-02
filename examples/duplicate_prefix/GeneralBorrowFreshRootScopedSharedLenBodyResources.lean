import duplicate_prefix.GeneralBorrowFreshRootScopedSharedLenBeforeReturn
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryResources
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntryHidden
import duplicate_prefix.LenBodyFromEntry
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedLenBodyResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open GeneralBorrowForestMixedLenBeforeReturn
theorem before_return
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
 :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree entry.allocation.extra tracker exprTag offset len
    ∃ (result : CompilerFrameContext.ActualFrame) (finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      (SuccessfulTrace.Trace cfg limits (Storage.withCurrent frames caller beforeMachine)
        (Storage.withCurrent (frames.push root) result finalMachine) ∧
      result.location = .mir ⟨1,1⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      result.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      result.extra.dataRace = none ∧
      result.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size root 11 RootCompilerFacts.usizeLayout ∧
      result.returnContinuation = .goto (some 3) .Continue ∧ result.vaList = #[] ∧
      finalMachine.memory = RetagEntry.updatedMemory beforeMachine.memory id entry borrowedTree ∧
      finalMachine.borrowTracker = some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧
      finalMachine.user.addresses = beforeMachine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = beforeMachine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.runtime.extras = beforeMachine.user.payload.payload.user.runtime.extras ) ∧ ReturnFacts options remaining span result finalMachine len
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ RootCache frames finalMachine ∧
      let fullGlobal := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
      DuplicatePrefixBorrowContract.RuntimeFacts borrowedTree fullGlobal ∧
      borrowedTree.roots = entry.allocation.extra.roots ∧ borrowedTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 ∧
      ∃ child node,borrowedTree.indexOfTag tracker.global.nextPointerTag = some child ∧
        borrowedTree.nodeAt child = some node ∧ node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive borrowedTree fullGlobal.protectedTags child input.selected input.maximum offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin borrowedTree child .Read offset (offset+len) := by
  obtain ⟨result,finalMachine,trace,facts,cache⟩ := GeneralBorrowFreshRootScopedSharedLenBeforeReturn.before_return
    options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled defaultMode fresh runtime input
    parentTagEq offsetEq lenEq bounds allocationSize valid live uncached noClocks ghost shallow cachedAddress present race
    thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source
    sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed
  obtain ⟨afterRuntime,capacity,growth,roots,held,tagFresh,child,lookup,parentPositive,childPositive,activity⟩ :=
    GeneralBorrowFreshRootScopedSharedFnEntryResources.resources entry.allocation.extra tracker {} id runtime input
  obtain ⟨hiddenChild,node,hiddenLookup,nodePresent,sameTag,hidden⟩ :=
    GeneralBorrowFreshRootScopedSharedFnEntryHidden.hidden entry.allocation.extra tracker {} id runtime input
  have same : hiddenChild = child := Option.some.inj (hiddenLookup.symm.trans lookup)
  subst hiddenChild
  refine ⟨result,finalMachine,trace,facts,cache,?_⟩
  dsimp only
  refine ⟨?_,?_,?_,child,node,?_,?_,sameTag,hidden,?_,?_⟩
  · simpa only [parentTagEq,offsetEq,lenEq] using afterRuntime
  · simpa only [parentTagEq,offsetEq,lenEq] using roots
  · simpa only [parentTagEq,offsetEq,lenEq] using growth
  · simpa only [parentTagEq,offsetEq,lenEq] using lookup
  · simpa only [parentTagEq,offsetEq,lenEq] using nodePresent
  · simpa only [parentTagEq,offsetEq,lenEq] using childPositive
  · simpa only [parentTagEq,offsetEq,lenEq] using activity
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedLenBodyResources
