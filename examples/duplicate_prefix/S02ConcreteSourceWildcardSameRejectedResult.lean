import duplicate_prefix.S02WildcardReturnSameCountInitial
import duplicate_prefix.S02WildcardReturnSameRejectedBody
namespace DuplicatePrefix.S02ConcreteSourceWildcardSameRejectedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Original rejected-call safety for concrete source and same-allocation
wildcard return. The shared body derives its actual operation outcomes. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) (rejected : count > len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨reference,firstFresh,destination,fresh,raw,query,node,post,_tag,_offset,_len,same,leaf,hidden,sourceId,destOffset,actual,capacity,nodes,tags⟩ :=
    S02WildcardReturnSameCountInitial.enters id tag address len count input nonempty sameAllocation returnWildcard
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have physicalId := sourceId.trans (binding.1.symm.trans sameAllocation)
  have trackerEq : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ := Option.some.inj destination.enabled.symm
  have different : destination.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag := by
    intro eq
    have values := congrArg (fun t : BorTag => t.value.toNat) eq
    rw [trackerEq] at values
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat = _ at values
    have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    omega
  obtain ⟨tracker,enabled,defaultMode⟩ := (S02SeparateDestinationReady.model_after_argument input reference firstFresh).defaultTracker
  have mode : destination.tracker.retagMode = .Default := (Option.some.inj (destination.enabled.symm.trans enabled)) ▸ defaultMode
  have separated := S02SameDestinationLiveTransport.actual_reference_disjoint id tag address len input nonempty sameAllocation reference
  have sourceStop : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt reference.storage.bounds reference.capacity.toNat_lt
  have returnStop : (destination.offset+1).toNat = destination.offset.toNat+1 := by
    simp only [UInt64.toNat_add,UInt64.toNat_one]
    apply Nat.mod_eq_of_lt
    have := destination.bounds;have := destination.capacity.toNat_lt;omega
  have disjoint : (reference.offset+len).toNat ≤ destination.offset.toNat ∨ (destination.offset+1).toNat ≤ reference.offset.toNat := by
    rw [sourceStop,returnStop,destOffset]
    exact separated
  exact S02WildcardReturnSameRejectedBody.result (Pointer.new (.concrete id tag) (Size.ofBytes address)) len count input reference current destination fresh
    changed owned query raw.selected raw.maximum node post rfl same hidden different sourceId physicalId disjoint capacity nodes tags mode rfl rfl rfl actual rejected
end
end DuplicatePrefix.S02ConcreteSourceWildcardSameRejectedResult
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardSameRejectedResult.result) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved concrete source same wildcard rejected dependency {dependency}"
