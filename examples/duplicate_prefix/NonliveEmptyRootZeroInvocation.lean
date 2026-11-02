import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.NonliveEmptyRootInvocationState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.NonliveEmptyRootZeroInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
/-- A genuine count-zero invocation for a non-null concrete empty reference
whose allocation metadata exists with a non-live-data kind. The argument's
allocation memory is not accessed; the separate canonical return slot is
protected, released and physically written. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo) (allocationInfo : before.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
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
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining+1) span precise implicitWrites
  obtain ⟨slotAllocation,call,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    NonliveEmptyRootInvocationEntry.enters options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset 0 nonzero before ghost shallow cachedAddress info allocationInfo nonlive enabled fresh race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let raw := RawRootInvocation.root before place race
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let tag := (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag
  let heldTracker := PositiveRootInvocationState.held tracker fresh slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted 0 {} id tracker.global.nextPointerTag slotId tag
  let initialMachine := NonliveEmptyRootInvocationState.enteredMachine rawMachine tracker fresh slotFresh slotId slotEntry slotRoot slotAllocation
  have call' : Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame initialMachine) := by
    rw [NonliveEmptyRootInvocationState.entered_eq] at call
    exact call
  obtain ⟨frameBody,frameIdentity,frameCallee,frameContinuation,frameReturn,frameVa,frameRace,frameBorrow,frameLocation⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted 0 {} id tracker.global.nextPointerTag slotId tag
  have frameSize : frame.locals.size=25 := PositiveRootInstalledFrame.size raw adjusted 0 {} id tracker.global.nextPointerTag slotId tag
  have valid0 : (0:MIR.LocalId)<frame.locals.size := by rw [frameSize];decide
  have slot0 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag ⟨0,by decide⟩
  have slot2 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag ⟨2,by decide⟩
  have slot3 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag ⟨3,by decide⟩
  have slot4 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag ⟨4,by decide⟩
  have slot5 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag ⟨5,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot0 slot2 slot3 slot4 slot5
  have allImmediate := PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race) adjusted 0 {} id tracker.global.nextPointerTag slotId tag
  let bM := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span initialMachine))
  let newEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {slotEntry with allocation:=slotAllocation}
  let bf : FrameState := (({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector slotId tag
  let releasedMemory := StackPopRelease.commitTree bM.memory slotId newEntry slotAllocation.extra
  let postTracker := {heldTracker with global:=heldTracker.global.endCall bf}
  let popped := GenericPopFrame.afterRelevanceAt #[] frame (ActualPopPlan.released bM releasedMemory heldTracker bf) 0
  let state : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩,popped⟩
  have heldFree := PositiveRootInvocationState.buffer_root_free tracker fresh slotFresh slotRoot slotParentDistinct slotDistinct slotFree
  have heldChild : heldTracker.global.protectedTags.contains tag = true := by simp [heldTracker,tag,PositiveRootInvocationState.held,registeredTracker,registeredGlobal,ProtectedTags.contains]
  have rawFacts := RawRootInvocation.preservation #[] before
  have rawInfo : rawMachine.memory.getAllocInfo id = .ok info := by rw [rawFacts.1];exact allocationInfo
  have initialInfo : initialMachine.memory.getAllocInfo id = .ok info :=
    (NonliveEmptyRootInvocationState.allocation_info_other rawMachine tracker fresh slotFresh slotId slotEntry slotRoot slotAllocation id (Ne.symm separate)).trans rawInfo
  have initialPresent : initialMachine.memory.live.find? (fun row => row.1 == slotId)=some (slotId,newEntry) := MemoryCopyBridge.live_lookup_replaced _ slotId newEntry
  have profile : RootPhysicalReturnPlan.Profile heldTracker.global.protectedTags bf.protectedTags.toList bM.memory releasedMemory := by
    apply RootPhysicalReturnPlan.Profile.nonlive id tracker.global.nextPointerTag info [(slotId,tag)] bM.memory releasedMemory initialInfo nonlive
    apply RootPhysicalReturnPlan.Profile.slot slotId slotRoot tag 1 true newEntry [] bM.memory releasedMemory
      initialPresent protectedTree heldFree heldChild slotDistinct (by decide)
    exact .nil _
  have rawActive : rawMachine.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have activeEntered : bM.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} := rawActive
  have addrState : state.machine.user.addresses=before.user.addresses := by
    change bM.user.addresses=before.user.addresses
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact rawFacts.2.2.2.1
  have backendState : state.machine.user.payload.payload.user.backend=.none := by
    change bM.user.payload.payload.user.backend=.none
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    exact rawFacts.2.2.2.2.2.2.2.1.trans noBackend
  have extrasState : state.machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras := by
    change bM.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2]
    exact rawFacts.2.2.2.2.2.2.2.2
  have initialGhost : initialMachine.user.payload.ghost=false := rawFacts.2.2.2.2.1.trans ghost
  have initialShallow : initialMachine.user.payload.validation=.Shallow := rawFacts.2.2.2.2.2.1.trans shallow
  have ghostState : state.machine.user.payload.ghost=false := by
    change bM.user.payload.ghost=false
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact initialGhost
  have shallowState : state.machine.user.payload.validation=.Shallow := by
    change bM.user.payload.validation=.Shallow
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact initialShallow
  have rootFree : postTracker.global.protectedTags.contains slotRoot=false := by
    rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact heldFree
  have childFree : postTracker.global.protectedTags.contains tag=false := by
    rw [StackPopRelease.end_call_contains]
    simp [bf,FrameState.addProtector]
  have uncheckedEntered : (config.terminators.getControl initialMachine.user).checkedArithmetic=false := by
    change (config.terminators.getControl rawMachine.user).checkedArithmetic=false
    rw [RootZeroInvocationState.raw_control]
    exact unchecked
  have noGcEntered : (config.terminators.getControl initialMachine.user).gcInterval=0 := by
    change (config.terminators.getControl rawMachine.user).gcInterval=0
    rw [RootZeroInvocationState.raw_control]
    exact noGc
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic=⟨Size.ofBytes 8⟩ := outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic=⟨Size.ofBytes 8⟩ := innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  have endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive=.ok (Size.ofBytes (slotBase+1)) := by
    rw [slotPointer]
    have added := size_add_ok (Size.ofBytes slotBase) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  have maskValid : InitMaskCopy.WellFormed slotAllocation.initializationMask := by rw [protectedMask];trivial
  obtain ⟨result,trace,terminal,safe,props⟩ := RootZeroComplete.complete outer inner options remaining span innerAccess innerWidth
    (by rw [innerRuntime];rfl) (by rw [innerRuntime,outerRuntime]) limits validityFuel debugOff validationEq
    frame initialMachine bM rfl uncheckedEntered noGcEntered fixed heldTracker bf rfl frameBorrow releasedMemory profile
    {thread with topUserRelevantFrame:=some 0} activeEntered state rfl (frameBody.trans raw.body) (frameIdentity.trans raw.identity)
    (frameCallee.trans raw.callee) frameLocation frameSize source (congrArg (fun row=>row.value) slot3)
    (congrArg (fun row=>row.value) slot4) (congrArg (fun row=>row.value) slot5)
    (congrArg (fun row=>row.layout) slot4) (congrArg (fun row=>row.layout) slot5)
    (congrArg (fun row=>row.value) slot2) (congrArg (fun row=>row.layout) slot2)
    initialGhost initialShallow mode valid0 (frameRace.trans raw.noClocks)
    (frameContinuation.trans (RawRootInvocation.control before place race).2.2.1) allImmediate
    (by rw [frameVa];rfl) place slotId slotRoot tag true slotBase 1 newEntry postTracker
    (congrArg (fun row=>row.value) slot0) (congrArg (fun row=>row.layout) slot0) rfl layout outerWidth (by decide) (by decide)
    (by rw [addrState];exact slotCached) initialPresent protectedSize protectedMutable maskValid (by rw [outerRuntime];rfl)
    (by rw [protectedLen,protectedSize];rfl) (by rw [protectedMask,protectedSize];rfl) protectedProv race backendState rfl
    (by change state.machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [extrasState];exact extras)
    rootFree childFree protectedTree slotPointer aligned (by rw [outerRuntime];rfl) outerAccess ghostState shallowState
    (by rw [frameReturn];rfl) (Size.ofBytes (slotBase+1)) endpoint
  exact ⟨Storage.withCurrent #[] frame initialMachine,CanonicalCopy.replaceAllocation state slotId slotEntry.kind result,call',trace,terminal,safe⟩

#print axioms invoke
end DuplicatePrefix.NonliveEmptyRootZeroInvocation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.NonliveEmptyRootZeroInvocation.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved nonlive empty zero invocation dependency {dependency}"
