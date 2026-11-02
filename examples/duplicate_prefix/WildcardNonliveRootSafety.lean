import duplicate_prefix.WildcardNonliveRootCallEquality
import duplicate_prefix.NonliveEmptyRootSafety
import duplicate_prefix.DuplicatePrefixCompletedCallResult
import duplicate_prefix.DuplicatePrefixEmptyReferenceInput
import duplicate_prefix.WildcardEmptyTargetClassification
namespace DuplicatePrefix.WildcardNonliveRootSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- An exposed exact-base wildcard hit to non-liveData metadata executes the
same genuine initialization as a concrete reference after canonical retagging.
The unchanged existing nonlive continuation proves every count through return.
This API is intermediate: lookup data is supplied by a raw metadata wrapper. -/
theorem invoke_known_metadata
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base count : UInt64) (nonzero : base ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (position : Nat) (positionValid : position < before.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap)
    (inverse : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (nonstrict : before.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.user.addresses.exposed.contains id = true)
    (allocLive : before.memory.isAllocLive id = true)
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
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (tags : Fin 6 → BorTag) (tagsDistinct : Function.Injective tags)
    (childEq : tracker.global.nextPointerTag = tags 1)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = tags 2)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = tags 3)
    (slotChildNot3 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 3)
    (slotRootNot3 : slotRoot ≠ tags 3)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes base))) 0 count place := by
  let parentTag := tracker.global.nextPointerTag
  obtain ⟨installed,done,call,trace,terminal,safety⟩ := NonliveEmptyRootSafety.invoke options limits remaining span
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base 0 count
    (by simpa only [UInt64.add_zero] using nonzero) before ghost shallow cachedAddress info allocationInfo nonlive
    enabled fresh race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned
    slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable
    storage maskLength provenance noBackend extras thread active noCache precise implicitWrites source mode unchecked
    noGc fixed fits tags tagsDistinct childEq thirdFresh fourthFresh thirdTag fourthTag slotChildNot3 slotRootNot3 budget dispatchFuel
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  have equal := WildcardNonliveRootCallEquality.call_equal options limits remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base count nonzero before ghost shallow cachedAddress
    info allocationInfo nonlive position positionValid ordered inverse nonstrict exposed allocLive enabled fresh race
    metadata notConstructed place thread active noCache
  simp only [UInt64.add_zero] at call
  have actual := equal.trans call
  exact DuplicatePrefixCompletedCallResult.of_trace options limits remaining span before
    (.pointer (Pointer.new .wildcard (Size.ofBytes base))) 0 count place installed done actual safety.1 trace terminal
/-- Nondata metadata is supplied by initial stored rows with source precedence.
The actual lookup equation and non-liveData kind are derived, never assumed. -/
theorem nondata_info {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (input : DuplicatePrefixEmptyReferenceInput.Metadata memory id none)
    (absent : memory.live.find? (fun row => row.1 == id) = none) :
    ∃ info, memory.getAllocInfo id = .ok info ∧ info.kind ≠ .liveData := by
  cases input with
  | live entry present parent => rw [absent] at present;cases present
  | functionRow gone present =>
    exact ⟨_,by simp only [MemoryState.getAllocInfo,gone,present,↓reduceIte];rfl,by intro bad;cases bad⟩
  | vaListRow gone noFunction present =>
    unfold MemoryState.hasVaListId at present
    exact ⟨_,by simp only [MemoryState.getAllocInfo,gone,noFunction,present,Bool.false_eq_true,↓reduceIte];rfl,by intro bad;cases bad⟩
  | nondataGlobal descriptor gone noFunction noVaList present kind =>
    unfold MemoryState.hasVaListId at noVaList
    rcases kind with kindEq | kindEq | kindEq
    all_goals exact ⟨_,by simp only [MemoryState.getAllocInfo,gone,noFunction,noVaList,present,kindEq,Bool.false_eq_true,↓reduceIte];rfl,by intro bad;cases bad⟩
  | dead entry gone noFunction noVaList noGlobal present =>
    unfold MemoryState.hasVaListId at noVaList
    exact ⟨_,by simp only [MemoryState.getAllocInfo,gone,noFunction,noVaList,noGlobal,present,Bool.false_eq_true,↓reduceIte];rfl,by intro bad;cases bad⟩

/-- Closes the exposed exact-base wildcard nondata-target branch admitted by
S01. Initial source metadata and recurring address coherence supply all lookup,
liveness and order facts internally. No data allocation is fabricated, and no
retag/call success or future state is assumed. Other wildcard hit/miss and
concrete/NoProv branches remain separate coverage obligations. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base count : UInt64) (nonzero : base ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (position : Nat) (positionValid : position < before.user.addresses.intToPtrMap.size)
    (coherent : GlobalAddressRecurringFormation.State before.memory before.user.addresses)
    (inverse : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (nonstrict : before.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.user.addresses.exposed.contains id = true)
    (metadataInput : DuplicatePrefixEmptyReferenceInput.Metadata before.memory id none)
    (noLocal : before.memory.live.find? (fun row => row.1 == id) = none)
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
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (tags : Fin 6 → BorTag) (tagsDistinct : Function.Injective tags)
    (childEq : tracker.global.nextPointerTag = tags 1)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = tags 2)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = tags 3)
    (slotChildNot3 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 3)
    (slotRootNot3 : slotRoot ≠ tags 3)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes base))) 0 count place := by
  have separate : slotId ≠ id := by
    intro same
    have conflict := slotPresent
    rw [same,noLocal] at conflict
    cases conflict
  obtain ⟨info,known,nonlive⟩ := nondata_info before.memory id metadataInput noLocal
  have live : before.memory.isAllocLive id = true :=
    coherent.live.1 ⟨base,id⟩ (Array.mem_of_getElem? inverse)
  exact invoke_known_metadata options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id tracker base count nonzero before ghost shallow cachedAddress position positionValid coherent.ordered inverse nonstrict exposed live
    info known nonlive enabled fresh race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned
    slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength
    provenance noBackend extras thread active noCache precise implicitWrites source mode unchecked noGc fixed fits tags tagsDistinct childEq
    thirdFresh fourthFresh thirdTag fourthTag slotChildNot3 slotRootNot3 budget dispatchFuel

end
end DuplicatePrefix.WildcardNonliveRootSafety
