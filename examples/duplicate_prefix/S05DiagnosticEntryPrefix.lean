import duplicate_prefix.S05DiagnosticRootInvocation
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix
namespace DuplicatePrefix.S05DiagnosticEntryPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments S05DiagnosticFnEntryScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The actual diagnostic root initialization followed by its nonzero pure MIR prefix. -/
theorem reaches_shared_site
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base n : UInt64) (nonzero : base ≠ 0)
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
    (source : PreparedContracts.SourceComparator) (countNonzero : n ≠ 0)
    (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
    ∃ (frame result : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
          .ok () (Storage.withCurrent #[] frame machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape frame result n ∧
      result.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ ∧
      result.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      let post := RootZeroCompleteState.tick options remaining span machine
      post.memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra (S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2)}) ∧
      post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      post.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime ∧
      post.user.payload.payload.user.types = before.user.payload.payload.user.types ∧
      post.dataRace = none ∧ post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧
      ∃ sharedTracker, post.borrowTracker = some sharedTracker ∧ sharedTracker.retagMode = .Default ∧
        sharedTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 10 ∧
        sharedTracker.global.protectedTags = (({} : ProtectedTags).insert (S05DiagnosticFnEntryRead.tag 8) .StrongProtector).insert
          (S05DiagnosticFnEntryRead.tag 9) .StrongProtector := by
  dsimp only
  obtain ⟨updated,actual,_⟩ := S05DiagnosticRootInvocation.enters options limits remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base n nonzero entry bounds before ghost shallow
    cachedAddress present enabled fresh tree parentEq nextEq protectedEq race metadata notConstructed retagCtx place layout
    slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh
    slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let raw := RawRootInvocation.root before place race
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) 2 ActualReferenceMetadata.reference).imm
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
  let argsMachine := resultMachine (RawRootInvocation.machine #[] before) tracker fresh id entry parentTag
  let argsFrame := RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted ({} : FrameState) id tracker.global.nextPointerTag) n
  let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let borrowed := ReturnProtection.borrowedState #[] changed owned argsMachine next slotFresh slotId slotEntry
    (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
  let machine := (CanonicalCopy.replaceAllocation borrowed slotId slotEntry.kind updated).machine
  let frame := PositiveRootInstalledFrame.installed raw adjusted n {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have shape := PositiveRootInstalledFrame.metadata raw adjusted n {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have size := PositiveRootInstalledFrame.size raw adjusted n {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted n {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  have all := PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race)
    adjusted n {} id tracker.global.nextPointerTag slotId next.global.nextPointerTag
  let finalTracker := registeredTracker (allocatedTracker next slotFresh) next.global.nextPointerTag
  have tracked : machine.borrowTracker = some finalTracker := rfl
  have finalMode : finalTracker.retagMode = .Default := mode
  obtain ⟨_,_,_,_,ghostEq,shallowEq,_,_,_⟩ := RawRootInvocation.preservation #[] before
  have machineUser : machine.user = (RawRootInvocation.machine #[] before).user := rfl
  have machineThreads : machine.threads = (RawRootInvocation.machine #[] before).threads := rfl
  have postGhost : machine.user.payload.ghost = false := by rw [machineUser,ghostEq]; exact ghost
  have postShallow : machine.user.payload.validation = .Shallow := by rw [machineUser,shallowEq]; exact shallow
  have postUnchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [machineUser,RootZeroInvocationState.raw_control]; exact unchecked
  have postNoGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [machineUser,RootZeroInvocationState.raw_control]; exact noGc
  have postFixed : machine.threads.fixedScheduling = true := by rw [machineThreads]; exact fixed
  obtain ⟨result,trace,preserved⟩ := S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals
    options limits remaining span source debugOff validityFuel validationEq frame machine n countNonzero
    (shape.1.trans raw.body) (shape.2.1.trans raw.identity) (shape.2.2.1.trans raw.callee)
    shape.2.2.2.2.2.2.2.2 size adjusted slots (shape.2.2.2.2.2.2.1.trans raw.noClocks) all
    finalTracker tracked finalMode postGhost postShallow postUnchecked postNoGc postFixed
  let finalTree := S05DiagnosticFnEntryArgument.finalTree entry.allocation.extra tracker parentTag 0 2
  let finalEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have first := StackPopRelease.lookup_commit_same (RawRootInvocation.machine #[] before).memory id entry finalTree
  have second := StackPopRelease.lookup_commit_other
    (StackPopRelease.commitTree (RawRootInvocation.machine #[] before).memory id entry finalTree)
    slotId id slotEntry finalEntry (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false) separate.symm first
  change borrowed.machine.memory.live.find? (fun row => row.1 == id) = some (id,finalEntry) at second
  have last := StackPopRelease.lookup_commit_other borrowed.machine.memory slotId id
    (⟨slotEntry.kind,updated⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind) finalEntry updated.extra separate.symm second
  have same : updated.setExtra updated.extra = updated := by cases updated; rfl
  have live : machine.memory.live.find? (fun row => row.1 == id) = some (id,finalEntry) := by
    simpa only [StackPopRelease.commitTree,same,CanonicalCopy.replaceAllocation,machine] using last
  have tick := RootZeroInvocationState.tick_fields options remaining span machine
  have tag10 : finalTracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 10 := by
    simp only [finalTracker,registeredTracker,registeredGlobal,allocatedTracker,next,
      TypedRetagGeneric.protectedGlobal,TypedRetagGeneric.allocatedGlobal,TypedRetagEmpty.successorTag]
    simp only [nextEq,S05DiagnosticFnEntryRead.tag]
    rfl
  have tags : finalTracker.global.protectedTags = (({} : ProtectedTags).insert (S05DiagnosticFnEntryRead.tag 8) .StrongProtector).insert
      (S05DiagnosticFnEntryRead.tag 9) .StrongProtector := by
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert
      (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) .StrongProtector = _
    simp only [TypedRetagEmpty.successorTag,protectedEq,nextEq,S05DiagnosticFnEntryRead.tag]
    rfl
  refine ⟨frame,result,machine,actual,trace,preserved,?_,preserved.slot12,?_,?_,?_,?_,?_,?_,?_,finalTracker,?_,finalMode,tag10,tags⟩
  · exact preserved.slot1.trans (by simpa only [Nat.reduceEqDiff,or_false,ite_false,ite_true] using slots ⟨1,by decide⟩)
  · rw [tick.1]; exact live
  · rw [tick.2.2.2.2.1,machineUser]
    rw [(RawRootInvocation.preservation #[] before).2.2.2.1]
    exact cachedAddress
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    change machine.user.payload.payload.user.types.metadata = _
    rw [machineUser,(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.1]
    exact metadata
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    change machine.user.payload.payload.user.types = _
    rw [machineUser]
    exact (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.1
  · rw [tick.2.2.1]
    change (RawRootInvocation.machine #[] before).dataRace = none
    exact (RawRootInvocation.preservation #[] before).2.2.1.trans race
  · exact (RootZeroCompleteState.tick_ghost options remaining span machine).trans postGhost
  · exact (RootZeroCompleteState.tick_shallow options remaining span machine).trans postShallow
  · rw [tick.2.1]; exact tracked
end
end DuplicatePrefix.S05DiagnosticEntryPrefix
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S05DiagnosticEntryPrefix.reaches_shared_site) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved diagnostic entry prefix dependency {dependency}"
