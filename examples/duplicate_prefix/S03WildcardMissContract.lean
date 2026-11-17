import duplicate_prefix.S03WildcardMissCallResources
import duplicate_prefix.S03WildcardMissConcreteZeroComplete
import duplicate_prefix.S03WildcardMissConcretePositiveComplete
import duplicate_prefix.S03WildcardMissWildcardZeroComplete
import duplicate_prefix.S03WildcardMissWildcardPositiveComplete

namespace DuplicatePrefix.S03WildcardMissContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The initial unresolved-address branch of a wildcard empty argument executes
its original call for every count and every original return provenance. The
lookup equation is an initial classifier case, never a future success premise. -/
theorem complete_of_miss {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (miss : before.user.addresses.allocIdFromAddr pointer.offset.bytes 0
      (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let packet := S03WildcardMissCallResources.of_contract input wildcard
  have mode := (S03WildcardEmptyClassification.candidate input.contract wildcard).2.nonstrict
  have normalized : Pointer.new .wildcard (Size.ofBytes pointer.offset.bytes) = pointer := by
    change (⟨pointer.offset,.wildcard⟩ : Pointer Provenance) = pointer
    rw [←wildcard]
  suffices result : DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes pointer.offset.bytes))) 0 count place by
    simpa only [normalized] using result
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete id tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun id => Provenance.concrete id tag) binding.1)
    by_cases zero : count = 0
    · subst count
      exact S03WildcardMissConcreteZeroComplete.complete limits before input.contract.model place input.contract.destination
        packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second tag concrete pointer.offset.bytes packet.nonzero
        mode miss packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq input.slice_not_constructed input.return_extras
        input.contract.thread input.contract.active input.contract.emptyHarnessCache
    · exact S03WildcardMissConcretePositiveComplete.complete limits before input.contract.model place input.contract.destination
        packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second tag concrete pointer.offset.bytes count packet.nonzero zero
        mode miss packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq packet.bodyFresh packet.bodyRoomNext
        packet.budget packet.dispatchEq input.slice_not_constructed input.return_extras input.contract.thread input.contract.active
        input.contract.emptyHarnessCache
  | wildcard =>
    by_cases zero : count = 0
    · subst count
      exact S03WildcardMissWildcardZeroComplete.complete limits before input.contract.model place input.contract.destination
        packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second provenance pointer.offset.bytes packet.nonzero
        mode miss packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq input.slice_not_constructed input.return_extras
        input.contract.thread input.contract.active input.contract.emptyHarnessCache
    · exact S03WildcardMissWildcardPositiveComplete.complete limits before input.contract.model place input.contract.destination
        packet.runtime packet.distinct packet.order packet.headroom packet.first packet.second provenance pointer.offset.bytes count packet.nonzero zero
        mode miss packet.dynamicFuel packet.validityFuel packet.dynamicEq packet.validityEq packet.bodyFresh packet.bodyRoomNext
        packet.budget packet.dispatchEq input.slice_not_constructed input.return_extras input.contract.thread input.contract.active
        input.contract.emptyHarnessCache

/-- Classify the original wildcard Candidate internally: every actual miss
finishes the original call; only selected allocation hits remain to dispatch. -/
theorem dispatch {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) (count : UInt64) :
    Nonempty (S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes) ∨
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases S03WildcardEmptyClassification.contract input.contract wildcard with miss | hits
  · exact Or.inr (complete_of_miss input wildcard miss count)
  · exact Or.inl hits

end
end DuplicatePrefix.S03WildcardMissContract
