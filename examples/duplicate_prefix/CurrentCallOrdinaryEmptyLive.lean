import duplicate_prefix.CurrentCallOrdinaryEmptyNonlive
import duplicate_prefix.CurrentCallEmptyLiveSafety
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyLive
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- The live zero-size source needs only its actual mapped parent, never a
source content family or permissions. SAME/different allocation is selected
internally from actual IDs, and all margins come from OrdinaryInput. -/
theorem concrete {options limits remaining span before place}
    (sourceId : AllocId) (parentTag : BorTag) (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 place)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (parent : DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra (some parentTag))
    (returnPresent : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker
      (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address)))):=by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧(∃base,before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩) ∧
    ZeroTarget before input.tracker sourceId (some parentTag) at empty
  obtain ⟨nonnull,⟨base,cached⟩,_⟩:=empty
  obtain ⟨packet⟩:=CurrentCallOrdinaryEmptyNonlive.return_packet input returnPresent
  obtain ⟨index,node,tagged,nodeAt⟩:=parent
  let offset:=address-base
  have addressEq : base+offset=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  have member : (sourceId,entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global:=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  have sourceRoom : entry.allocation.extra.nodes.size+3≤4294967295:=by
    have room : entry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ member
    omega
  have tagRoom : input.tracker.global.nextPointerTag.value.toNat+3<18446744073709551615:=by have room:=packet.tagRoom;omega
  by_cases same : sourceId=packet.physical.id
  · have liveP : before.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,packet.physical.entry):=by
      simpa only [←same] using packet.physical.live
    have entryEq : entry=packet.physical.entry:=(Prod.mk.inj (Option.some.inj (live.symm.trans liveP))).2
    let start:=address-packet.physical.base
    have startEq : packet.physical.base+start=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address packet.physical.base
    have boolMember : (packet.physical.id,packet.physical.entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some packet.physical.live)
    have nodeRoom : packet.B.allocation.extra.nodes.size+4<65536:=by
      rw [←packet.allocation]
      have room : packet.physical.entry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ boolMember
      omega
    have result:=CurrentCallEmptyLiveSafety.concrete_same options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
      place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct parentTag index node
      (by rw [←entryEq];exact tagged) (by rw [←entryEq];exact nodeAt) start (by rw [startEq];exact nonnull) tagRoom nodeRoom packet.ready
      (options.place.dynamicFuel-1) (options.limits.validation-1)
      (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins count
      (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)
    simpa only [startEq,←same] using result
  · have result:=CurrentCallEmptyLiveSafety.concrete_different options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
      place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct sourceId same entry live base cached
      sourceRuntime sourceRoom parentTag index node tagged nodeAt offset (by rw [addressEq];exact nonnull) tagRoom packet.nodeRoom packet.ready
      (options.place.dynamicFuel-1) (options.limits.validation-1)
      (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins count
      (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)
    simpa only [addressEq] using result
/-- Wildcard live HIT retains the actual exposed source choice and delegates
both SAME/different ID paths to the existing zero-source all-count producer. -/
theorem wildcard {options limits remaining span before place}
    (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (hit : CurrentCallEmptyClassification.Hit before input.tracker address)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==hit.id)=some (hit.id,entry))
    (returnPresent : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes address)))):=by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧before.user.addresses.provenanceMode≠.strict ∧_ at empty
  obtain ⟨nonnull,nonstrict,_⟩:=empty
  obtain ⟨packet⟩:=CurrentCallOrdinaryEmptyNonlive.return_packet input returnPresent
  have sizeEq : hit.info.size=entry.allocation.byteSize:=by
    have known:=hit.known
    simp only [MemoryState.getAllocInfo,live] at known
    exact (congrArg AllocationInfo.size (Except.ok.inj known)).symm
  let offset:=address-hit.base
  have addressEq : hit.base+offset=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address hit.base
  have member : (hit.id,entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global:=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  have sourceRoom : entry.allocation.extra.nodes.size+3≤4294967295:=by
    have room : entry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ member
    omega
  have tagRoom : input.tracker.global.nextPointerTag.value.toNat+3<18446744073709551615:=by have room:=packet.tagRoom;omega
  by_cases same : hit.id=packet.physical.id
  · have liveP : before.memory.live.find? (fun row=>row.1==hit.id)=some (hit.id,packet.physical.entry):=by
      simpa only [←same] using packet.physical.live
    have entryEq : entry=packet.physical.entry:=(Prod.mk.inj (Option.some.inj (live.symm.trans liveP))).2
    have cachedP : before.user.addresses.baseAddr.find? (fun row=>row.allocId==hit.id)=some ⟨hit.id,packet.physical.base⟩:=by
      simpa only [←same] using packet.physical.cachedBase
    have baseEq : hit.base=packet.physical.base:=congrArg (fun row=>row.address) (Option.some.inj (hit.cached.symm.trans cachedP))
    let start:=address-packet.physical.base
    have startEq : packet.physical.base+start=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address packet.physical.base
    have boolMember : (packet.physical.id,packet.physical.entry)∈before.memory.live.toList:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some packet.physical.live)
    have nodeRoom : packet.B.allocation.extra.nodes.size+4<65536:=by
      rw [←packet.allocation]
      have room : packet.physical.entry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ boolMember
      omega
    have geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap address packet.physical.base packet.physical.id packet.physical.entry.allocation.byteSize:=by
      rw [←same,←entryEq,←baseEq,←sizeEq]
      exact hit.geometry
    have result:=CurrentCallEmptyLiveSafety.wildcard_same options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
      place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct
      start (by rw [startEq];exact nonnull) nonstrict (by rw [startEq];exact geometry) (by rw [←same];exact hit.exposed)
      tagRoom nodeRoom packet.ready (options.place.dynamicFuel-1) (options.limits.validation-1)
      (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins count
      (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)
    simpa only [startEq] using result
  · have result:=CurrentCallEmptyLiveSafety.wildcard_different options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
      place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct hit.id same entry live hit.base hit.cached
      sourceRuntime sourceRoom offset (by rw [addressEq];exact nonnull) nonstrict (by rw [addressEq,←sizeEq];exact hit.geometry) hit.exposed
      tagRoom packet.nodeRoom packet.ready (options.place.dynamicFuel-1) (options.limits.validation-1)
      (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins count
      (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)
    simpa only [addressEq] using result
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyLive
