import duplicate_prefix.S03LiveEmptyContractData
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.S03WildcardLiveInit

namespace DuplicatePrefix.S03WildcardLiveContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original consistent caller contract produces actual live empty
initialization for every count, when argument and concrete return place share
an allocation. No allocator Input, post-argument Input or future permission is
supplied by the caller. The Hit packet is initial metadata derived by Candidate classification; no resolver success is supplied. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentWildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (sameAllocation : hit.id = input.contract.destination.id)
    (tag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (count : UInt64) :
    let original := input.contract.destination
    let model := input.contract.model
    let argumentOffset := pointer.offset.bytes-original.base
    ∃ (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global),
    ∃ (first : original.tracker.global.nextPointerTag.value < 18446744073709551615)
      (second : (S03LiveEmptyState.next original.tracker first).global.nextPointerTag.value < 18446744073709551615),
    ∃ (slot : WildcardHitPoolRoot.Slot original.entry.allocation.extra)
      (positive : DuplicatePrefixBorrowAuthorization.Positive (slot.after original.tracker.global.nextPointerTag) (S03LiveEmptyState.next original.tracker first).global.protectedTags
        original.source original.selectedRoot original.maximum original.offset 1) (updated : Allocation Provenance BorrowTree),
    let raw := RawRootInvocation.root before place model.noDataRace
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete original.id original.tracker.global.nextPointerTag) (Size.ofBytes (original.base+argumentOffset))) 0 ActualReferenceMetadata.reference).imm
    let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone raw adjusted {} original.id original.tracker.global.nextPointerTag) count
    let current := S03WildcardLiveState.argumentsMachine original first slot
    let input := S03WildcardLiveState.input original first slot tag returnConcrete
      (GeneralBorrowParentTagInvariant.fresh _ _ runtime) positive
    let owned := ({} : FrameState).addProtector original.id original.tracker.global.nextPointerTag
    let tree := GeneralBorrowRawFnEntryArgument.finalTree (slot.after original.tracker.global.nextPointerTag) (S03LiveEmptyState.next original.tracker first) tag original.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
      (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
      (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    let after := Storage.withCurrent #[]
      (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
        {args.frame with location := .unwinding ⟨601⟩} owned original.id
          (S03LiveEmptyState.next original.tracker first).global.nextPointerTag with location := .unwinding ⟨559⟩})
      (S04ProtectUninit.finished current place input #[] {args.frame with location := .unwinding ⟨601⟩}
        owned second tree updated).machine
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) 0),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () after ∧
    updated.extra = written ∧ updated.byteSize = original.entry.allocation.byteSize ∧
    updated.len = original.entry.allocation.len ∧ updated.mutability = .Mut ∧
    InitMaskCopy.WellFormed updated.initializationMask ∧
    updated.initializationMask.len = original.entry.allocation.initializationMask.len ∧
    (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
    Nonempty (S03EmptyTagState.Data written original.tracker.global.nextPointerTag slot.index) ∧
    S04ReturnReleaseInactive.Quiescent written slot.index ∧
    (owned.addProtector original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag).protectedTags =
      #[(original.id,original.tracker.global.nextPointerTag),(original.id,(S03LiveEmptyState.next original.tracker first).global.nextPointerTag)] ∧
    S04ReturnReleaseParent.HiddenFrame written
      (owned.addProtector original.id (S03LiveEmptyState.next original.tracker first).global.nextPointerTag) ∧
    ∃ parent child node, written.indexOfTag tag = some parent ∧
      written.indexOfTag (S03LiveEmptyState.next original.tracker first).global.nextPointerTag = some child ∧
      written.nodeAt child = some node ∧ node.tag = (S03LiveEmptyState.next original.tracker first).global.nextPointerTag ∧
      node.parent = some parent ∧ node.isExposed = false ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags (some child)
        original.selectedRoot original.maximum original.offset 1) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write original.offset (original.offset+1) := by
  let original := input.contract.destination
  let model := input.contract.model
  let argumentOffset := pointer.offset.bytes-original.base
  have candidate := S03WildcardEmptyClassification.candidate input.contract argumentWildcard
  have nonnull := candidate.1
  obtain ⟨runtime,distinct,order,headroom,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validityEq⟩ := S03LiveEmptyContractData.fuels input.contract
  have address : original.base+argumentOffset = pointer.offset.bytes := by
    change original.base+(pointer.offset.bytes-original.base)=pointer.offset.bytes
    rw [UInt64.add_comm,UInt64.sub_add_cancel]
  have cached := hit.cached
  rw [sameAllocation] at cached
  have bases := Option.some.inj (cached.symm.trans original.cachedBase)
  have baseEq : hit.base = original.base := congrArg Miri.Memory.AllocAddresses.BaseAddressEntry.address bases
  have known := hit.known
  rw [sameAllocation] at known
  have liveInfo : before.memory.getAllocInfo original.id =
      .ok ⟨original.entry.allocation.byteSize,original.entry.allocation.align,.liveData,original.entry.allocation.mutability⟩ := by
    simp only [MemoryState.getAllocInfo,original.live]
    rfl
  have infos := Except.ok.inj (known.symm.trans liveInfo)
  have sizes : hit.info.size = original.entry.allocation.byteSize := congrArg AllocationInfo.size infos
  have inverse := hit.geometry
  rw [sameAllocation,baseEq,sizes] at inverse
  have normalized : Pointer.new .wildcard (Size.ofBytes (original.base+argumentOffset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.wildcard⟩ : Pointer Provenance) = pointer
    rw [←argumentWildcard]
  obtain ⟨slot,positive,updated,actual,properties⟩ := S03WildcardLiveInit.enters limits before model place original runtime distinct order headroom
    first second candidate.2.nonstrict argumentOffset (by rw [address];exact inverse)
    (by rw [←sameAllocation];exact hit.exposed) tag returnConcrete count (by rw [address];exact nonnull)
    dynamicFuel validityFuel dynamicEq validityEq input.slice_not_constructed input.return_extras
    input.contract.thread input.contract.active input.contract.emptyHarnessCache
  refine ⟨runtime,first,second,slot,positive,updated,?_,properties⟩
  simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,normalized] using actual

end
end DuplicatePrefix.S03WildcardLiveContract
