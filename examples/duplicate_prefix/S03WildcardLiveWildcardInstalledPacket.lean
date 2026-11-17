import duplicate_prefix.S03WildcardLiveWildcardState
import duplicate_prefix.S03WildcardLiveEntry
import duplicate_prefix.S03LiveWildcardPostArguments
import duplicate_prefix.S03LiveEmptyContractData
import duplicate_prefix.S03WildcardEmptyClassification

namespace DuplicatePrefix.S03WildcardLiveWildcardInstalledPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- An initial same-allocation wildcard argument and wildcard return place
produce the actual initialized frame and complete current body/Return packet.
All local margins follow from the original sixteen-slot resource budget. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentWildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (sameAllocation : hit.id = input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (count : UInt64) :
    ∃ frame machine,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer pointer) 0),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      Nonempty (S03LiveWildcardPacket.Packet options remaining span frame machine place pointer.offset.bytes count) := by
  let original := input.contract.destination
  let model := input.contract.model
  let argumentOffset := pointer.offset.bytes-original.base
  have candidate := S03WildcardEmptyClassification.candidate input.contract argumentWildcard
  obtain ⟨runtime,distinct,order,headroom,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  change original.entry.allocation.extra.nodes.size+2 < 65536 at headroom
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
  let slot := S03WildcardLiveState.slot original.entry.allocation.extra original.tracker.global runtime (by omega)
  obtain ⟨⟨positive⟩,currentRuntime,currentOrder,currentDistinct,currentRoom,⟨zero⟩,tagFresh,different⟩ :=
    S03WildcardLiveState.facts original runtime first slot headroom distinct order
  let current := S03WildcardLiveState.argumentsMachine original first slot
  let currentInput := S03WildcardLiveWildcardState.input original first slot returnWildcard positive
  let raw := RawRootInvocation.root before place model.noDataRace
  have member : (original.id,original.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some original.live)
  have initialRoom := input.contract.resources.nodeRoom (original.id,original.entry) member
  dsimp only at initialRoom
  have growth := slot.size original.tracker.global.nextPointerTag
  have growthBound : slot.growth ≤ 1 := by cases slot <;> simp [WildcardHitPoolRoot.Slot.growth]
  have nodeRoom : currentInput.entry.allocation.extra.nodes.size+3 < 65536 := by
    change (slot.after original.tracker.global.nextPointerTag).nodes.size+3 < 65536
    omega
  have sameTracker : input.contract.tracker = original.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans original.enabled)
  have initialTags := input.contract.resources.tagRoom
  rw [sameTracker] at initialTags
  have successor := GenericFunctionEntryNumerics.successor_value original.tracker.global.nextPointerTag first
  have tagRoom : currentInput.tracker.global.nextPointerTag.value.toNat+3 < 2^64 := by
    change (TypedRetagEmpty.successorTag original.tracker.global.nextPointerTag first).value.toNat+3 < 2^64
    omega
  have activeNow : current.threads.activeThread? = some {input.contract.thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 input.contract.thread 0 input.contract.active
  obtain ⟨frame,machine,tail,⟨packet⟩⟩ := S03LiveWildcardPostArguments.run limits current
    (S03WildcardLiveState.model original model first slot) place currentInput currentRuntime currentDistinct currentOrder
    nodeRoom second tagRoom returnWildcard original.tracker.global.nextPointerTag slot.index zero raw
    (RawRootInvocation.locals before place model.noDataRace) rfl rfl rfl (original.base+argumentOffset) count
    input.return_extras input.slice_not_constructed {input.contract.thread with topUserRelevantFrame := some 0} activeNow rfl
  have actual := S03WildcardLiveEntry.after_tail limits before model place original runtime first slot
    candidate.2.nonstrict argumentOffset (by rw [address];exact inverse)
    (by rw [←sameAllocation];exact hit.exposed) count (by rw [address];exact candidate.1)
    dynamicFuel validityFuel dynamicEq validityEq input.slice_not_constructed input.contract.thread input.contract.active
    input.contract.emptyHarnessCache (Storage.withCurrent #[] frame machine) tail
  refine ⟨frame,machine,?_,?_⟩
  · simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,normalized] using actual
  · exact ⟨by simpa only [address] using packet⟩

end
end DuplicatePrefix.S03WildcardLiveWildcardInstalledPacket
