import duplicate_prefix.CurrentCallLenReadEntry

namespace DuplicatePrefix.CurrentCallLenReadBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath GeneralRangeMapOrigins
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
open GeneralBorrowForestMixedLenBeforeReturn CurrentCallLenArgumentCopy
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Current reader resources drive the actual call step, helper body and Return
location. No caller operation-success certificate or legacy callback bank is used. -/
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
    (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (model : CurrentCallResourceNormalization.ParentInterpretation entry.allocation.extra completion)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (selectedPosition : Nat) (selected sourceIndex reader : UniIndex) (selectedNode readerNode : TreeNode)
    (primaryBelow : ∀ root,entry.allocation.extra.roots[0]?=some root → Below completion root sourceIndex)
    (selectedSlot : entry.allocation.extra.roots[selectedPosition]?=some selected)
    (selectedPresent : entry.allocation.extra.nodes.get selected=some selectedNode)
    (sourcePath : Path entry.allocation.extra selected sourceIndex)
    (readerPresent : entry.allocation.extra.nodes.get reader=some readerNode)
    (readerPath : Path entry.allocation.extra selected reader) (readerTag : readerNode.tag=exprTag)
    (short : entry.allocation.extra.nodes.size<65536) (nodeRoom : entry.allocation.extra.nodes.size+1≤4294967295)
    (owned : OwnedOn (S05CurrentReadProtectorRelease.Authority entry.allocation.extra completion tracker.global.protectedTags selected sourceIndex reader)
      offset (offset+len) entry.allocation.extra.locations)
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
    (cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller valid) machine)
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView current)))
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
    let borrowedTree := finalTree entry.allocation.extra tracker exprTag offset len
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
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm ∧ RootCache frames finalMachine := by
  have treeBounds : offset.toNat+len.toNat≤entry.allocation.extra.locations.size.bytes.toNat := by rw [allocationSize];exact bounds
  have lenNonzero : len ≠ 0 := by intro zero;rw [zero] at positive;contradiction
  have result := CurrentCallLenReadEntry.invoke entry.allocation.extra completion tracker.global {} id runtime model distinct
    selectedPosition selected sourceIndex reader selectedNode readerNode primaryBelow selectedSlot selectedPresent sourcePath readerPresent readerPath
    fresh short nodeRoom offset len lenNonzero owned treeBounds
  have readCompleted : (readOperation entry.allocation.extra tracker exprTag offset len).status=.Completed := by
    simpa only [readerTag,readOperation,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
      GlobalState.addProtector,TypedBorrowSteps.registeredGlobal] using result.2.1
  have childCompleted : (childOperation entry.allocation.extra tracker exprTag offset len).outcome=.ok () := by
    simpa only [readerTag,childOperation,readOperation,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
      GlobalState.addProtector,TypedBorrowSteps.registeredGlobal,GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead] using result.2.2.1
  exact CurrentCallLenArgumentCopy.before_return options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits
    frames caller machine tracker enabled defaultMode fresh readCompleted childCompleted bounds allocationSize
    valid live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata cacheOrigins
    sourceBody identity callee located source sourceValid sourceLive sourceCached backend beforeMachine machineEq unchecked noGc fixed

end
end DuplicatePrefix.CurrentCallLenReadBody
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallLenReadBody.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved narrow Len body dependency {dependency}"
