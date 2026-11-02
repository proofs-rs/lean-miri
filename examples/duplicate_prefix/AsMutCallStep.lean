import duplicate_prefix.AsMutUncachedCall
import duplicate_prefix.AsMutPtrReturn
namespace DuplicatePrefix.AsMutCallStep
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutEntry AsMutCallTerminator
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open AsMutUncachedCall
theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine))
      (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let initial := Storage.withCurrent frames caller machine
    let before := Storage.withCurrent frames (cachedCaller caller destValid) (AsMutPtrReturn.accountedMachine options remaining span machine)
    let destination := (LocalPlaces.localRuntimePlace frames.size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () initial =
      ((Storage.withCurrent (frames.push (cachedCaller caller destValid))
        (initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine), .ok true) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames caller machine
  let next := AsMutPtrReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent frames caller next
  have nextGhost : next.user.payload.ghost = false := by rw [AsMutPtrReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [AsMutPtrReturn.accounted_validation];exact shallow
  have nextBackend : next.user.payload.payload.user.backend = .none := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact backend
  have nextAddress : next.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact cachedAddress
  have nextMetadata : (EvalProjectionMachine.arrays.get nextState).metadata = PreparedReflection.actual.runtime := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact metadata
  have nextConstructed : (EvalProjectionMachine.arrays.get nextState).entries.any (·.value.ty == 4) = false := by
    unfold nextState next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact notConstructed
  have effect := AsMutUncachedCall.call_uncached options limits remaining budget dispatchFuel span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq tags distinct id entry capacity base offset len tree allocationSize positive nonzero
    signedFits bounds frames caller next tracker enabled defaultMode mask nextTag fresh body identity callee located source
    valid16 value16 cached16 destValid old destLive uncached callerClocks nextGhost nextShallow
    nextAddress present race nextBackend nextMetadata nextConstructed thread index current active top topPresent
  have accounting := SourceControl.before_terminator cfg limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
  have blockAt : caller.body.basicBlocks[6]? = some block := by rw [body];simp [block]
  have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
  dsimp only
  apply GenericCallStages.source_step cfg limits () before nextState _ caller ⟨6,8⟩ block
    HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue sourceKind fnSpan
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement source_call accounting' effect
  simp [Storage.withCurrent,nextState]

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual asmut step dependency {dependency}"
end
end DuplicatePrefix.AsMutCallStep
