import duplicate_prefix.S05DiagnosticLenCall
import duplicate_prefix.MetadataCallStep
import duplicate_prefix.LenBodyFromEntry
namespace DuplicatePrefix.S05DiagnosticLenBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess LenUncachedFrontend
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual caller terminator step, including source-control accounting. -/
theorem entry_step
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
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (treeEq : entry.allocation.extra = S05DiagnosticLenRead.tree)
    (parentEq : exprTag = S05DiagnosticFnEntryRead.tag 10)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 11)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (valid : 11 < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[11].value = .live (.immediate old))
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
    let cfg := config options remaining span
    let state := Storage.withCurrent frames (cachedCaller caller valid) machine
    let destination := (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller valid) 11 RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := S05DiagnosticLenInstall.finalTree entry.allocation.extra tracker exprTag offset len
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames caller beforeMachine) =
      ((Storage.withCurrent (frames.push (cachedCaller caller valid))
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine),.ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames caller beforeMachine
  let nextState := Storage.withCurrent frames caller machine
  have effect := S05DiagnosticLenCall.positive options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits frames caller machine tracker enabled fresh treeEq parentEq nextEq protectedEq offsetEq lenEq bounds valid old live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := by
    simpa only [nextState,before,machineEq,PtrMetadataReturn.accountedMachine,SourceControl.accounted,Storage.withCurrent,cfg] using accounting
  let block := RootBody.reflected.body.body.basicBlocks[2]'(by decide +kernel)
  have blockAt : caller.body.basicBlocks[2]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[12]? = none := by with_unfolding_all rfl
  apply GenericCallStages.source_step cfg limits () before nextState _ caller ⟨2,12⟩ block
    LenHelper.resolved.function #[LenEvaluateCall.argument] ⟨11,#[]⟩ (some 3) .Continue LenCallFrontend.sourceKind LenCallFrontend.fnSpan
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement LenCallFrontend.source_call accounting' effect
  simp [Storage.withCurrent,nextState]

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
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let root := cachedCaller caller valid
    let borrowedTree := S05DiagnosticLenInstall.finalTree entry.allocation.extra tracker exprTag offset len
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
  let borrowedTree := S05DiagnosticLenInstall.finalTree entry.allocation.extra tracker exprTag offset len
  have entered := entry_step options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits
    frames caller machine tracker enabled fresh treeEq parentEq nextEq protectedEq offsetEq lenEq bounds
    valid .uninit live uncached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame
    metadata notConstructed sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
  apply LenBodyFromEntry.before_return_full_data options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id entry base offset len exprTag positive nonzero signedFits bounds
    frames caller machine tracker enabled defaultMode fresh borrowedTree allocationSize valid live uncached noClocks ghost shallow
    cachedAddress present race thread index current active top presentFrame metadata notConstructed
    sourceBody identity callee located source sourceValid sourceLive sourceCached backend
    beforeMachine machineEq unchecked noGc fixed
  simpa only [LenEntryShape.initialized,Bool.false_eq_true,Bool.true_eq,↓reduceIte] using entered

#print axioms entry_step
#print axioms before_return
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticLenBody." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic len body dependency {dependency}"
end
end DuplicatePrefix.S05DiagnosticLenBody
