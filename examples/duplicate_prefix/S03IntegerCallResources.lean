import duplicate_prefix.S05ConsistentCallSpecification
import duplicate_prefix.S03IntegerZeroState

namespace DuplicatePrefix.S03IntegerCallResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Initial local facts extracted from the existing consistent integer-empty
contract. No call result, future metadata or future permission is stored. -/
structure Packet {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place) where
  nonzero : address ≠ 0
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.contract.destination.entry.allocation.extra input.contract.destination.tracker.global
  distinct : input.contract.destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.contract.destination.entry.allocation.extra
  headroom : input.contract.destination.entry.allocation.extra.nodes.size+1 < 65536
  first : input.contract.destination.tracker.global.nextPointerTag.value < 18446744073709551615
  second : (ReferenceBorrowDriver.allocatedTracker input.contract.destination.tracker first).global.nextPointerTag.value < 18446744073709551615
  dynamicFuel : Nat
  validityFuel : Nat
  dynamicEq : options.place.dynamicFuel = dynamicFuel+1
  validityEq : options.limits.validation = validityFuel+1
  bodyFresh : (RootZeroInvocationState.held input.contract.destination.tracker first second).global.nextPointerTag.value < 18446744073709551615
  bodyRoomNext : (RootZeroInvocationState.held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat+1 < 18446744073709551615
  budget : Nat
  dispatchEq : limits.callDispatch = budget+1

def of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place) : Packet input := by
  have same : input.contract.tracker = input.contract.destination.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans input.contract.destination.enabled)
  have member : (input.contract.destination.id,input.contract.destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.contract.destination.live)
  have bound := input.contract.resources.tagRoom
  rw [same] at bound
  have first : input.contract.destination.tracker.global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change input.contract.destination.tracker.global.nextPointerTag.value.toNat < 18446744073709551615;omega)
  have successor := GenericFunctionEntryNumerics.successor_value input.contract.destination.tracker.global.nextPointerTag first
  have second : (ReferenceBorrowDriver.allocatedTracker input.contract.destination.tracker first).global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag input.contract.destination.tracker.global.nextPointerTag first).value.toNat < 18446744073709551615
    omega
  have workPositive : 0 < work before 0 := by unfold work;omega
  have dyn := input.contract.resources.dynamicFuel
  have valid := input.contract.resources.configuredFuel.2.2.2
  have dispatch := input.contract.resources.executionFuel.1
  have successor2 := GenericFunctionEntryNumerics.successor_value
    (ReferenceBorrowDriver.allocatedTracker input.contract.destination.tracker first).global.nextPointerTag second
  have bodyTag : (RootZeroInvocationState.held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat =
      input.contract.destination.tracker.global.nextPointerTag.value.toNat+2 := by
    change (TypedRetagEmpty.successorTag (ReferenceBorrowDriver.allocatedTracker input.contract.destination.tracker first).global.nextPointerTag second).value.toNat = _
    change (ReferenceBorrowDriver.allocatedTracker input.contract.destination.tracker first).global.nextPointerTag.value.toNat =
      input.contract.destination.tracker.global.nextPointerTag.value.toNat+1 at successor
    omega
  refine ⟨?_,?_,input.contract.runtime.roots _ member,input.contract.runtime.parentTags _ member,?_,first,second,
    options.place.dynamicFuel-1,options.limits.validation-1,by omega,by omega,?_,?_,limits.callDispatch-1,by omega⟩
  · cases reference : input.contract.reference with
    | empty zero metadata =>
      exact metadata.1
    | positive pointer encoding positive => cases encoding
  · have facts : DuplicatePrefixBorrowContract.RuntimeFacts input.contract.destination.entry.allocation.extra input.contract.tracker.global :=
      ⟨input.contract.runtime.formed _ member,input.contract.runtime.coherent _ member,input.contract.runtime.possible _ member,
        input.contract.resources.tagsBelow _ member⟩
    rw [same] at facts
    exact facts
  · have room := input.contract.resources.nodeRoom _ member
    dsimp only at room
    omega
  · apply UInt64.lt_iff_toNat_lt.mpr
    change (RootZeroInvocationState.held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  · omega

end
end DuplicatePrefix.S03IntegerCallResources
