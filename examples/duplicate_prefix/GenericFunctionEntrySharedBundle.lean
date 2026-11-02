import duplicate_prefix.GenericFunctionEntryToShared
import duplicate_prefix.GenericFunctionEntryBundle
import duplicate_prefix.GenericFunctionEntryClean

namespace DuplicatePrefix.GenericFunctionEntrySharedBundle
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem enter
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset len count : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (data : GenericAsMutPtrEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
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
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (countPositive : (0 : UInt64) < count)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) entry.allocation.extra.locations)
    (successorFresh : GeneralBorrowProtector.Fresh entry.allocation.extra (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag)
    (successorDifferent : tracker.global.nextPointerTag ≠ (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag)
 :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} id tracker.global.nextPointerTag
      slotId (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag
    ∃ (slotAllocation : Allocation Provenance BorrowTree) (result : CompilerFrameContext.ActualFrame),
      let initialMachine := GenericFunctionEntryState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry parentTag offset len
        slotFresh slotId slotEntry slotRoot slotAllocation
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame initialMachine) ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span initialMachine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count ∧
      GenericFunctionEntryToShared.Ready result adjusted count ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector
        slotId (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag) ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree slotRoot (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      slotAllocation.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot slotEntry.allocation ∧
      slotAllocation.mutability = .Mut ∧
      (let tree := GenericAsMutPtrArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
       let index := GeneralBorrowFreshMutableStages.slot_index data.slot
       let finalMachine := RootZeroCompleteState.tick options remaining span initialMachine
       ∃ treeMetadata : GenericFunctionEntryMetadata.Output entry.allocation.extra tracker parentTag offset len data,
         finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra tree}) ∧
         finalMachine.borrowTracker = some (GenericFunctionEntryState.held tracker fresh slotFresh) ∧
         GeneralRangeMapOrigins.OwnedOn
           (GeneralBorrowRange.LocationOwned tree (GenericFunctionEntryState.held tracker fresh slotFresh).global.protectedTags index .Write)
           offset (offset+len) tree.locations ∧
         GeneralBorrowFreshActiveWithin.ActiveWithin tree index .Write offset (offset+len) ∧
         (∀ future, GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping future →
           GeneralBorrowProtector.Fresh entry.allocation.extra future → tracker.global.nextPointerTag ≠ future →
           GeneralBorrowTagMap.Fresh tree.tagMapping future ∧ GeneralBorrowProtector.Fresh tree future) ∧
         (∀ query, entry.allocation.extra.nodes.get query = none →
           query ≠ GeneralBorrowFreshMutableStages.slot_index data.slot →
           GeneralBorrowFreshFutureClean.Clean entry.allocation.extra query →
           tree.nodes.get query = none ∧ GeneralBorrowFreshFutureClean.Clean tree query)) := by
  dsimp only
  obtain ⟨slotAllocation,result,call,trace,shape,ready,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    GenericFunctionEntryToShared.enters_shared_boundary options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset len count nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      data capacity race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
      source mode countPositive unchecked noGc fixed
  let rawMachine := RawRootInvocation.machine #[] before
  let initialMachine := GenericFunctionEntryState.enteredMachine rawMachine tracker fresh id entry parentTag offset len
    slotFresh slotId slotEntry slotRoot slotAllocation
  have bounded : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [capacity];exact bounds
  obtain ⟨treeMetadata,lookup,borrow,owned,active,future⟩ := GenericFunctionEntryBundle.prepare rawMachine tracker fresh id entry parentTag offset len
    (UInt64.pos_iff_ne_zero.mp positive) data bounded clean slotFresh successorFresh successorDifferent slotId slotEntry slotRoot slotAllocation (Ne.symm separate)
  have tick : (RootZeroCompleteState.tick options remaining span initialMachine).memory = initialMachine.memory ∧
      (RootZeroCompleteState.tick options remaining span initialMachine).borrowTracker = initialMachine.borrowTracker := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl⟩
  refine ⟨slotAllocation,result,call,trace,shape,ready,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable,
    treeMetadata,?_,?_,owned,active,future,?_⟩
  · rw [tick.1]
    exact lookup
  · rw [tick.2]
    exact borrow
  · intro query vacant different cleanQuery
    exact GenericFunctionEntryClean.future entry.allocation.extra tracker parentTag offset len
      (UInt64.pos_iff_ne_zero.mp positive) data bounded query vacant different cleanQuery

end DuplicatePrefix.GenericFunctionEntrySharedBundle
