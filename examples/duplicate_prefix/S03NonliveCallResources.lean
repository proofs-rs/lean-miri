import duplicate_prefix.S03LiveEmptyContractData
import duplicate_prefix.S03NonliveZeroState
import duplicate_prefix.S03NonliveTagCatalog

namespace DuplicatePrefix.S03NonliveCallResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

def held (tracker : MachineHooks.BorrowState)
    (first : tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (TypedRetagGeneric.protectedGlobal tracker.global first).nextPointerTag.value < 18446744073709551615) :=
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global first,tracker.retagMode⟩
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker next second) next.global.nextPointerTag

private theorem tag_eq {left right : BorTag} (same : left.value.toNat = right.value.toNat) : left = right := by
  cases left with
  | mk left positive =>
    cases right with
    | mk right positive' =>
      have equal : left = right := UInt64.toNat_inj.mp same
      subst right
      rfl

/-- Every local numeric/configuration requirement is extracted from the
existing initial contract. The finite tag names satisfy the old component
interfaces and add no independent premise to the public nonlive case. -/
structure Packet {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) where
  base : UInt64
  offset : UInt64
  cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,base⟩
  address : base+offset = pointer.offset.bytes
  nonzero : base+offset ≠ 0
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.contract.destination.entry.allocation.extra input.contract.destination.tracker.global
  distinct : input.contract.destination.entry.allocation.extra.roots.toList.Nodup
  order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.contract.destination.entry.allocation.extra
  headroom : input.contract.destination.entry.allocation.extra.nodes.size+1 < 65536
  first : input.contract.destination.tracker.global.nextPointerTag.value < 18446744073709551615
  second : (TypedRetagGeneric.protectedGlobal input.contract.destination.tracker.global first).nextPointerTag.value < 18446744073709551615
  dynamicFuel : Nat
  validityFuel : Nat
  dynamicEq : options.place.dynamicFuel = dynamicFuel+1
  validityEq : options.limits.validation = validityFuel+1
  bodyFresh : (held input.contract.destination.tracker first second).global.nextPointerTag.value < 18446744073709551615
  bodyRoom : (held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat+1 < 18446744073709551615
  tags : Fin 6 → BorTag
  tagsDistinct : Function.Injective tags
  firstTag : tags 1 = input.contract.destination.tracker.global.nextPointerTag
  bodyTag : (held input.contract.destination.tracker first second).global.nextPointerTag = tags 2
  lenTag : (ReferenceBorrowDriver.allocatedTracker (held input.contract.destination.tracker first second) bodyFresh).global.nextPointerTag = tags 3
  budget : Nat
  dispatchEq : limits.callDispatch = budget+1

theorem exists_of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (parentTag : BorTag) (concrete : pointer.provenance = .concrete argumentId parentTag) :
    Nonempty (Packet input argumentId) := by
  have candidate : DuplicatePrefixEmptyReferenceInput.Candidate
      (imageContext options before input.contract.tracker) before.memory before.user.addresses pointer.withOptionalProvenance := by
    cases reference : input.contract.reference with
    | empty zero metadata => exact metadata
    | positive value encoding positive => have bad := positive.borrow.positive;contradiction
  simp only [DuplicatePrefixEmptyReferenceInput.Candidate,Pointer.withOptionalProvenance,concrete] at candidate
  obtain ⟨base,cached⟩ := candidate.2.1
  let offset := pointer.offset.bytes-base
  have address : base+offset = pointer.offset.bytes := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel _ _
  obtain ⟨runtime,distinct,order,headroom,first,second⟩ := S03LiveEmptyContractData.resources input.contract
  obtain ⟨dynamicFuel,validityFuel,dynamicEq,validityEq⟩ := S03LiveEmptyContractData.fuels input.contract
  have same : input.contract.tracker = input.contract.destination.tracker :=
    Option.some.inj (input.contract.runtime.enabled.symm.trans input.contract.destination.enabled)
  have room := input.contract.resources.tagRoom
  rw [same] at room
  have firstValue := GenericFunctionEntryNumerics.successor_value input.contract.destination.tracker.global.nextPointerTag first
  have secondValue := GenericFunctionEntryNumerics.successor_value
    (TypedRetagGeneric.protectedGlobal input.contract.destination.tracker.global first).nextPointerTag second
  have bodyValue : (held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat =
      input.contract.destination.tracker.global.nextPointerTag.value.toNat+2 := by
    change (TypedRetagEmpty.successorTag (TypedRetagGeneric.protectedGlobal input.contract.destination.tracker.global first).nextPointerTag second).value.toNat = _
    change (TypedRetagGeneric.protectedGlobal input.contract.destination.tracker.global first).nextPointerTag.value.toNat =
      input.contract.destination.tracker.global.nextPointerTag.value.toNat+1 at firstValue
    omega
  have bodyFresh : (held input.contract.destination.tracker first second).global.nextPointerTag.value < 18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change (held input.contract.destination.tracker first second).global.nextPointerTag.value.toNat < 18446744073709551615;omega)
  let tags := S03NonliveTagCatalog.catalog input.contract.destination.tracker.global.nextPointerTag room
  have thirdValue := GenericFunctionEntryNumerics.successor_value (held input.contract.destination.tracker first second).global.nextPointerTag bodyFresh
  have workPositive : 0 < work before 0 := by unfold work;omega
  have dispatch := input.contract.resources.executionFuel.1
  refine ⟨⟨base,offset,cached,address,(by rw [address];exact candidate.1),runtime,distinct,order,by omega,first,second,
    dynamicFuel,validityFuel,dynamicEq,validityEq,bodyFresh,by omega,tags,S03NonliveTagCatalog.injective _ _,
    S03NonliveTagCatalog.first _ _,?_,?_,limits.callDispatch-1,by omega⟩⟩
  · apply tag_eq
    rw [S03NonliveTagCatalog.value,bodyValue]
    rfl
  · apply tag_eq
    change (TypedRetagEmpty.successorTag (held input.contract.destination.tracker first second).global.nextPointerTag bodyFresh).value.toNat = _
    rw [thirdValue,S03NonliveTagCatalog.value,bodyValue]
    rfl

def of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (argumentId : AllocId) (parentTag : BorTag) (concrete : pointer.provenance = .concrete argumentId parentTag) :
    Packet input argumentId := Classical.choice (exists_of_contract input argumentId parentTag concrete)

end
end DuplicatePrefix.S03NonliveCallResources
