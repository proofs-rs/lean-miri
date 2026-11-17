import duplicate_prefix.CurrentCallOrdinaryReturnLive
import duplicate_prefix.CurrentCallEmptyNonliveSafety
import duplicate_prefix.CurrentCallEmptyWildcardNonliveSafety
import duplicate_prefix.CurrentCallEmptyClassification
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyNonlive
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Internal live-return case selection from the actual lookup. The latent
alternative is ruled out by its declared absence, not a caller choice. -/
theorem return_packet {options limits remaining span before argument place}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (present : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    Nonempty (CurrentCallOrdinaryReturnLive.Packet input) := by
  rcases input.returnBacking with live | latent
  · exact CurrentCallOrdinaryReturnLive.form input live
  · obtain ⟨entry,found⟩:=present
    rw [latent.1] at found
    cases found

/-- Initial OrdinaryInput fields supply every physical, ownership, runtime and
budget premise of the metadata-backed absent CONCRETE branch. The remaining
hypotheses identify only this initial representation case. -/
theorem concrete {options limits remaining span before place}
    (sourceId : AllocId) (parentTag : BorTag) (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before
      (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes address))) 0 place)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId (some parentTag))
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
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
  obtain ⟨packet⟩:=return_packet input returnPresent
  let offset:=address-base
  have addressEq : base+offset=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address base
  have result:=CurrentCallEmptyNonliveSafety.invoke options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
    sourceId parentTag base offset count (by rw [addressEq];exact nonnull) cached metadata absent place packet.physical packet.data 0 packet.B
    packet.pointer packet.allocation packet.runtime packet.binding packet.distinct packet.tagRoom packet.nodeRoom packet.ready input.cacheOrigins
    (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
    (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) (by have positive:=packet.dispatchPositive;omega)
  simpa only [addressEq] using result

/-- Exposed wildcard HIT uses the SAME actual computation as the concrete
nonlive branch. Raw classifier data retain actual pointer provenance/geometry;
no source family or independent operational-success premise is introduced. -/
theorem wildcard {options limits remaining span before place}
    (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (hit : CurrentCallEmptyClassification.Hit before input.tracker address)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory hit.id none)
    (absent : before.memory.live.find? (fun row=>row.1==hit.id)=none)
    (returnPresent : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes address)))):=by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧before.user.addresses.provenanceMode≠.strict ∧
    GlobalAddressRecurringFormation.State before.memory before.user.addresses ∧_ at empty
  obtain ⟨nonnull,nonstrict,coherent,_⟩:=empty
  obtain ⟨packet⟩:=return_packet input returnPresent
  let offset:=address-hit.base
  have addressEq : hit.base+offset=address:=by rw [UInt64.add_comm];exact UInt64.sub_add_cancel address hit.base
  have result:=CurrentCallEmptyWildcardNonliveSafety.invoke options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady
    hit.id hit.base offset count (by rw [addressEq];exact nonnull) hit.cached metadata absent hit.info hit.known
    (by rw [addressEq];exact hit.geometry) nonstrict hit.exposed coherent place packet.physical packet.data 0 packet.B
    packet.pointer packet.allocation packet.runtime packet.binding packet.distinct packet.tagRoom packet.nodeRoom packet.ready input.cacheOrigins
    (options.place.dynamicFuel-1) (options.limits.validation-1) (limits.callDispatch-1)
    (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) (by have positive:=packet.dispatchPositive;omega)
  simpa only [addressEq] using result
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyNonlive
