import duplicate_prefix.CurrentCallOrdinaryEmptyNonlive
import duplicate_prefix.CurrentCallEmptyIntegerSafety
import duplicate_prefix.CurrentCallEmptyMissSafety
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyUnlocated
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallOrdinaryInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- The actual provenance-free zero-source branch is derived from ordinary
physical input. No source allocation, family, protector or wildcard cast. -/
theorem integer {options limits remaining span before place} (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.integer address) 0 place)
    (returnPresent : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.integer address)):=by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  have nonnull : address≠0:=empty.1
  obtain ⟨packet⟩:=CurrentCallOrdinaryEmptyNonlive.return_packet input returnPresent
  exact CurrentCallEmptyIntegerSafety.invoke options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady address count nonnull
    place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct
    (by have room:=packet.tagRoom;omega) packet.nodeRoom packet.ready
    (options.place.dynamicFuel-1) (options.limits.validation-1)
    (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins
    (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)

/-- The initial query-MISS proof is produced by EmptyClassification. It feeds
the saved actual wildcard computation, with distinct provenance from integer. -/
theorem miss {options limits remaining span before place} (address count : UInt64)
    (input : OrdinaryInput options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 place)
    (queryMiss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (returnPresent : ∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==input.returnFamily.allocation)=some (input.returnFamily.allocation,entry)) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have empty : EmptySource before input.tracker (DuplicatePrefixSliceArgument.placePointer (.pointer (Pointer.new .wildcard (Size.ofBytes address)))):=by
    rcases input.source with empty | positive
    · exact empty.2.1
    · exact False.elim (positive.1 rfl)
  change address≠0 ∧before.user.addresses.provenanceMode≠.strict ∧_ at empty
  obtain ⟨nonnull,nonstrict,_⟩:=empty
  obtain ⟨packet⟩:=CurrentCallOrdinaryEmptyNonlive.return_packet input returnPresent
  exact CurrentCallEmptyMissSafety.invoke options limits remaining span before input.tracker input.model input.runtime.enabled input.stackReady address count nonnull nonstrict queryMiss
    place packet.physical packet.data 0 packet.B packet.pointer packet.allocation packet.runtime packet.binding packet.distinct
    (by have room:=packet.tagRoom;omega) packet.nodeRoom packet.ready
    (options.place.dynamicFuel-1) (options.limits.validation-1)
    (by have positive:=packet.dynamicPositive;omega) (by have positive:=packet.validationPositive;omega) input.cacheOrigins
    (limits.callDispatch-1) (by have positive:=packet.dispatchPositive;omega)
end
end DuplicatePrefix.CurrentCallOrdinaryEmptyUnlocated
