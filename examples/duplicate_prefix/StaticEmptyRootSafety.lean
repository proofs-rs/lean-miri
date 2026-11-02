import duplicate_prefix.StaticEmptyRootCallEquivalence
import duplicate_prefix.ConcreteEmptyRootSafety

/-! Genuine invocations for every UInt64 count from a lazy compiler STATIC global.
The raw descriptor is non-TLS and non-extern, and an explicit exported initializer
row determines the source allocation. The actual call materializes that image
during argument retagging before reusing the proved physical-return and NoUB
suffix. SupportedImage admits arbitrary finite ordered disjoint in-bounds
relocations to cached compiler-memory or declared non-TLS, non-extern static
targets; initialization masks and source mutability are preserved. Root-tag,
address, compiler metadata and physical return-slot coherence remain explicit.
Missing initializer queries, TLS/extern sources, byte-fragment provenance,
unknown allocation IDs and wildcard references are outside this theorem. -/
namespace DuplicatePrefix.StaticEmptyRootSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset count : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag) (rootUnprotected : tracker.global.protectedTags.contains parentTag = false)
    (source : Allocation CtfeProvenance Unit) (definition : Nat)
    (initializer : PreparedReflection.actual.image.initializers.find? (·.1 == definition) = some (definition,source))
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr)
    (rootCached : tracker.global.rootTag? id = some parentTag) (race : before.dataRace = none)
    (noExtras : (before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (descriptor : before.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
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
    (sourceComparator : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (tags : Fin 6 → BorTag) (tagsDistinct : Function.Injective tags)
    (parentEq : parentTag = tags 0) (childEq : tracker.global.nextPointerTag = tags 1)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = tags 2)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = tags 3)
    (slotChildNot3 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 3)
    (slotRootNot3 : slotRoot ≠ tags 3)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  obtain ⟨ctx,actualPointers⟩ := GlobalEmptyReferenceContext.exists_context options remaining span precise implicitWrites
  obtain ⟨converted,facts,callEq⟩ := StaticEmptyRootCallEquivalence.call_eq options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset count nonzero before
    ghost shallow cachedAddress enabled fresh distinct rootUnprotected source definition initializer supported rootCached race noExtras absent
    noFunction noVaList descriptor metadata notConstructed place thread active noCache
  let prepared := StaticEmptyRootCopy.preparedMachine options before id parentTag source converted
  let entry := StaticEmptyRootCopy.entry parentTag source converted
  have present : prepared.memory.live.find? (fun row => row.1 == id) = some (id,entry) :=
    MemoryCopyBridge.live_lookup_replaced before.memory id entry
  have size : entry.allocation.byteSize = Size.ofBytes source.byteSize.bytes := facts.size
  have slotPrepared : prepared.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry) := by
    rw [StaticEmptyRootPrepared.live_other options before id slotId parentTag source converted separate]
    exact slotPresent
  have extrasPrepared : prepared.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) =
      some (slotId,⟨none,#[]⟩) := by
    rw [StaticEmptyRootPrepared.extras_other options before id slotId parentTag source converted separate]
    exact extras
  have control : (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl prepared.user =
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨installed,done,call,trace,stop,safe⟩ := ConcreteEmptyRootSafety.invoke options limits remaining span
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset source.byteSize.bytes count
    nonzero entry prepared ghost shallow cachedAddress present enabled fresh distinct rootUnprotected rfl size race
    metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree
    slotSize slotPrepared separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength
    provenance noBackend extrasPrepared thread active noCache precise implicitWrites sourceComparator mode
    (by rw [control];exact unchecked) (by rw [control];exact noGc) fixed fits tags tagsDistinct parentEq childEq
    thirdFresh fourthFresh thirdTag fourthTag slotChildNot3 slotRootNot3 budget dispatchFuel
  exact ⟨installed,done,callEq.trans call,trace,stop,safe⟩

end DuplicatePrefix.StaticEmptyRootSafety

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.StaticEmptyRootSafety.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved genuine lazy global invocation dependency {dependency}"
