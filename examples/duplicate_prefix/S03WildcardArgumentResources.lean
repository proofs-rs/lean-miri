import duplicate_prefix.S03LiveEmptyContractData
import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.EmptyCallTimeFuelShape

namespace DuplicatePrefix.S03WildcardArgumentResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Local original-data resources common to live and materializable wildcard
argument hits. This packet contains no selected target or operation result. -/
structure Packet {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place) where
  nonnull : pointer.offset.bytes ≠ 0
  addressMode : before.user.addresses.provenanceMode ≠ .strict
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.contract.destination.entry.allocation.extra input.contract.destination.tracker.global
  distinct : input.contract.destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.contract.destination.entry.allocation.extra
  returnRoom : input.contract.destination.entry.allocation.extra.nodes.size+1 < 65536
  first : input.contract.destination.tracker.global.nextPointerTag.value < 18446744073709551615
  second : (S03LiveEmptyState.next input.contract.destination.tracker first).global.nextPointerTag.value < 18446744073709551615
  tagMargin : input.contract.destination.tracker.global.nextPointerTag.value.toNat+16 < 2^64
  dynamicFuel : Nat
  validityFuel : Nat
  budget : Nat
  dynamicEq : options.place.dynamicFuel = dynamicFuel+1
  validityEq : options.limits.validation = validityFuel+1
  dispatchEq : limits.callDispatch = budget+1

theorem exists_of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) : Nonempty (Packet input) := by
  have candidate := S03WildcardEmptyClassification.candidate input.contract wildcard
  obtain ⟨runtime,distinct,order,room,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,budget,dynamicEq,validityEq,dispatchEq⟩ := EmptyCallTimeFuelShape.derive input.contract.resources
  have same : input.contract.tracker = input.contract.destination.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans input.contract.destination.enabled)
  have tags := input.contract.resources.tagRoom
  rw [same] at tags
  exact ⟨⟨candidate.1,candidate.2.nonstrict,runtime,distinct,order,by omega,first,second,tags,
    dynamicFuel,validityFuel,budget,dynamicEq,validityEq,dispatchEq⟩⟩

def of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) : Packet input := Classical.choice (exists_of_contract input wildcard)

end
end DuplicatePrefix.S03WildcardArgumentResources
