import duplicate_prefix.PositiveRootCompleteInvocation
import duplicate_prefix.PositiveRootRejectedInvocation
import duplicate_prefix.PositiveRootZeroInvocation

namespace DuplicatePrefix.PositiveRootCanonicalSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- All counts for positive canonical slices. Fresh-tag/resource contracts are
uniform; the maximum-copy-size bound is derived from the accepted guard.
Arbitrary caller borrow/provenance histories remain a separate obligation. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset len capacity count : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
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
    (bufferStorage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (bufferMaskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (bufferMaskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (bufferInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len)))
    (bufferProvenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (bufferStorageFits : entry.allocation.len+64 < 18446744073709551616)
    (bufferMutable : entry.allocation.mutability = .Mut)
    (bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
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
  by_cases notZero : count = 0
  · subst count
    exact PositiveRootZeroInvocation.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset len capacity nonzero entry positive signedFits bounded bounds before ghost shallow cachedAddress present enabled fresh distinct rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache precise implicitWrites bufferParentDistinct2 source mode unchecked noGc fixed fits
  · by_cases tooLarge : count > len/2
    · exact PositiveRootRejectedInvocation.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset len capacity count nonzero entry positive signedFits bounded bounds before ghost shallow cachedAddress present enabled fresh distinct rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache precise implicitWrites bufferParentDistinct2 source mode unchecked noGc fixed fits notZero tooLarge tags tagsDistinct parentEq childEq thirdFresh fourthFresh thirdTag fourthTag newUnprotected slotChildNot2 slotChildNot3 slotRootNot3 budget dispatchFuel
    · have within : count ≤ len/2 := UInt64.le_iff_toNat_le.mpr
        (Nat.le_of_not_gt (fun greater => tooLarge (UInt64.lt_iff_toNat_lt.mpr greater)))
      obtain ⟨installed,done,updated,call,trace,empty,terminal,safe,stored,encoded,initialized,mutable⟩ :=
        PositiveRootCompleteInvocation.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset len capacity count nonzero entry positive signedFits bounded bounds before ghost shallow cachedAddress present enabled fresh distinct rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache precise implicitWrites bufferParentDistinct2 source mode unchecked noGc fixed fits notZero within tags tagsDistinct parentEq childEq thirdFresh fourthFresh thirdTag fourthTag newUnprotected slotChildNot2 slotChildNot3 slotRootNot3 free4 slotChildNot4 fifthTag fifthFresh sixthTag sixthFresh budget dispatchFuel bufferStorage bufferMaskValid bufferMaskLen bufferInitialized bufferProvenance bufferStorageFits bufferMutable bufferExtras statementFuel
      exact ⟨installed,done,call,trace,terminal,safe⟩

end DuplicatePrefix.PositiveRootCanonicalSafety
#print axioms DuplicatePrefix.PositiveRootCanonicalSafety.invoke
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootCanonicalSafety.invoke) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved all-count positive invocation dependency {dependency}"
