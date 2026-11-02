import duplicate_prefix.S03LiveEmptyInit
import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S03LiveEmptyContractData
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- For the live same-allocation case, the original empty candidate supplies
the concrete parent's presence. Other source suppliers contradict the already
known live row; no additional parent restriction is added to the contract. -/
theorem parent_present
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before (.pointer pointer) 0 place)
    (tag : BorTag) (concrete : pointer.provenance = .concrete input.destination.id tag) :
    pointer.offset.bytes ≠ 0 ∧ ∃ parent node,
      input.destination.entry.allocation.extra.indexOfTag tag = some parent ∧
      input.destination.entry.allocation.extra.nodeAt parent = some node := by
  have candidate : Candidate (imageContext options before input.tracker) before.memory before.user.addresses pointer.withOptionalProvenance := by
    cases reference : input.reference with
    | empty zero metadata => exact metadata
    | positive value encoding positive =>
      have bad := positive.borrow.positive
      contradiction
  simp only [Candidate,Pointer.withOptionalProvenance,concrete] at candidate
  refine ⟨candidate.1,?_⟩
  obtain ⟨_,metadata⟩ := candidate.2
  rcases metadata with known | ⟨source,root,absent,_⟩
  · cases known with
    | live entry live parent =>
      have same : entry = input.destination.entry := congrArg Prod.snd (Option.some.inj (live.symm.trans input.destination.live))
      subst entry
      exact parent
    | functionRow absent _ => rw [input.destination.live] at absent;contradiction
    | vaListRow absent _ _ => rw [input.destination.live] at absent;contradiction
    | nondataGlobal _ absent _ _ _ _ => rw [input.destination.live] at absent;contradiction
    | dead _ absent _ _ _ _ => rw [input.destination.live] at absent;contradiction
  · rw [input.destination.live] at absent
    contradiction

/-- All live-entry local resources come from the original sixteen-slot
budget and current runtime, with the next fresh tag derived arithmetically. -/
theorem resources
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before argument 0 place) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.destination.entry.allocation.extra input.destination.tracker.global ∧
    input.destination.entry.allocation.extra.roots.toList.Nodup ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.destination.entry.allocation.extra ∧
    input.destination.entry.allocation.extra.nodes.size+2 < 65536 ∧
    ∃ first : input.destination.tracker.global.nextPointerTag.value < 18446744073709551615,
      (S03LiveEmptyState.next input.destination.tracker first).global.nextPointerTag.value < 18446744073709551615 := by
  have same : input.tracker = input.destination.tracker := Option.some.inj (input.runtime.enabled.symm.trans input.destination.enabled)
  have state : DuplicatePrefixRuntimeInput.OrderedState before input.destination.tracker := same ▸ input.runtime
  have member : (input.destination.id,input.destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.destination.live)
  have below := input.resources.tagsBelow (input.destination.id,input.destination.entry) member
  rw [same] at below
  have room := input.resources.nodeRoom (input.destination.id,input.destination.entry) member
  dsimp only at room
  have tags := input.resources.tagRoom
  rw [same] at tags
  have first : input.destination.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change input.destination.tracker.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  have successor := GenericFunctionEntryNumerics.successor_value input.destination.tracker.global.nextPointerTag first
  refine ⟨⟨state.formed _ member,state.coherent _ member,state.possible _ member,below⟩,
    state.roots _ member,state.parent_order _ _ input.destination.live,by omega,first,?_⟩
  change (TypedRetagEmpty.successorTag input.destination.tracker.global.nextPointerTag first).value < 18446744073709551615
  apply UInt64.lt_iff_toNat_lt.mpr
  change (TypedRetagEmpty.successorTag input.destination.tracker.global.nextPointerTag first).value.toNat < 18446744073709551615
  omega

/-- Positive initial dynamic/validation fuel is a consequence of the raw work
budget, rather than an additional call-domain condition. -/
theorem fuels
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before argument 0 place) :
    ∃ dynamicFuel validityFuel, options.place.dynamicFuel = dynamicFuel+1 ∧ options.limits.validation = validityFuel+1 := by
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before 0 := by
    unfold DuplicatePrefixCallSpecification.work
    omega
  have dynamic := input.resources.dynamicFuel
  have validity := input.resources.configuredFuel.2.2.2
  exact ⟨options.place.dynamicFuel-1,options.limits.validation-1,by omega,by omega⟩

end
end DuplicatePrefix.S03LiveEmptyContractData
