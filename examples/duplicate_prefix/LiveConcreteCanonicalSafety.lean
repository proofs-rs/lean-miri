import duplicate_prefix.PositiveRootCanonicalSafety
import duplicate_prefix.ConcreteEmptyRootSafety

namespace DuplicatePrefix.LiveConcreteCanonicalSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Genuine invocation safety for all counts and all signed-size-bounded lengths
of live concrete canonical slices. Empty slices require no buffer byte-storage,
initialization, provenance-mask, mutability or copy-extra contract, and no slice
bounds contract. The canonical tree, return-slot, metadata and uniform resource
contracts remain explicit; arbitrary caller histories are not covered here. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset len capacity count : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (signedFits : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : (0 : UInt64) < len → offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag) (rootUnprotected : tracker.global.protectedTags.contains parentTag = false)
    (tree : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity) (race : before.dataRace = none)
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
    (bufferParentDistinct2 : parentTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (tags : Fin 6 → BorTag) (tagsDistinct : Function.Injective tags)
    (parentEq : parentTag = tags 0) (childEq : tracker.global.nextPointerTag = tags 1)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = tags 2)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = tags 3)
    (newUnprotected : tracker.global.protectedTags.contains (tags 2) = false)
    (slotChildNot2 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 2)
    (slotChildNot3 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 3)
    (slotRootNot3 : slotRoot ≠ tags 3)
    (free4 : tracker.global.protectedTags.contains (tags 4)=false)
    (slotChildNot4 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 4)
    (fifthTag : TypedRetagEmpty.successorTag (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag fourthFresh=tags 4)
    (fifthFresh : (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag.value<18446744073709551615)
    (sixthTag : TypedRetagEmpty.successorTag (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag fifthFresh=tags 5)
    (sixthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id) fifthFresh).global.nextPointerTag.value<18446744073709551615)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (bufferStorage : (0 : UInt64) < len → entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (bufferMaskValid : (0 : UInt64) < len → InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (bufferMaskLen : (0 : UInt64) < len → entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (bufferInitialized : (0 : UInt64) < len → InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len)))
    (bufferProvenance : (0 : UInt64) < len → ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (bufferStorageFits : (0 : UInt64) < len → entry.allocation.len+64 < 18446744073709551616)
    (bufferMutable : (0 : UInt64) < len → entry.allocation.mutability = .Mut)
    (bufferExtras : (0 : UInt64) < len → before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (statementFuel : limits.validation = validityFuel+1) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  dsimp only
  by_cases empty : len = 0
  · subst len
    exact ConcreteEmptyRootSafety.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset capacity count nonzero entry before ghost shallow cachedAddress present enabled fresh distinct
      rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned
      slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength
      provenance noBackend extras thread active noCache precise implicitWrites source mode unchecked noGc fixed fits
      tags tagsDistinct parentEq childEq thirdFresh fourthFresh thirdTag fourthTag slotChildNot3 slotRootNot3 budget dispatchFuel
  · have positive : (0 : UInt64) < len := UInt64.pos_iff_ne_zero.mpr empty
    exact PositiveRootCanonicalSafety.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset len capacity count nonzero entry positive signedFits bounded (bounds positive) before ghost shallow
      cachedAddress present enabled fresh distinct rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry
      slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree
      mutable storage maskLength provenance noBackend extras thread active noCache precise implicitWrites bufferParentDistinct2 source mode
      unchecked noGc fixed fits tags tagsDistinct parentEq childEq thirdFresh fourthFresh thirdTag fourthTag newUnprotected slotChildNot2
      slotChildNot3 slotRootNot3 free4 slotChildNot4 fifthTag fifthFresh sixthTag sixthFresh budget dispatchFuel
      (bufferStorage positive) (bufferMaskValid positive) (bufferMaskLen positive) (bufferInitialized positive) (bufferProvenance positive)
      (bufferStorageFits positive) (bufferMutable positive) (bufferExtras positive) statementFuel

end DuplicatePrefix.LiveConcreteCanonicalSafety
#print axioms DuplicatePrefix.LiveConcreteCanonicalSafety.invoke
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LiveConcreteCanonicalSafety.invoke) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved all-length live canonical invocation dependency {dependency}"
