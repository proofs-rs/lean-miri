import duplicate_prefix.S02SeparateDestinationAuthorization
import duplicate_prefix.GeneralBorrowFnEntryRegistrationRuntime
import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.S03IntegerZeroState

namespace DuplicatePrefix.S02SeparateDestinationReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The current global tag state after the argument's actual FnEntry
registration still satisfies the destination allocation's full runtime facts.
The destination tree is unchanged in the distinct-allocation branch. -/
theorem runtime_after_argument_registration
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64}
    {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before argument len place)
    (fresh : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixBorrowContract.RuntimeFacts input.contract.destination.entry.allocation.extra
      (TypedRetagGeneric.protectedGlobal input.contract.tracker.global fresh) := by
  let destination := input.contract.destination
  have member : (destination.id,destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some destination.live)
  have old : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra
      input.contract.tracker.global := {
    formed := input.contract.runtime.formed (destination.id,destination.entry) member
    coherent := input.contract.runtime.coherent (destination.id,destination.entry) member
    possible := input.contract.runtime.possible (destination.id,destination.entry) member
    below := input.contract.resources.tagsBelow (destination.id,destination.entry) member }
  obtain ⟨_,_,_,runtime,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    destination.entry.allocation.extra input.contract.tracker.global ({} : FrameState)
    destination.id fresh old
  simpa only [GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
    TypedRetagGeneric.protectedGlobal,TypedRetagGeneric.allocatedGlobal,
    GlobalState.addProtector] using runtime

/-- All local graph and headroom facts required by the general concrete
return-protection proof on the actual post-argument destination Input. -/
theorem local_facts_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    {id : AllocId} {tag : BorTag} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry tag reference.offset len) place)
    (entry : destination.entry = input.contract.destination.entry) :
    DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global ∧
    destination.entry.allocation.extra.roots.toList.Nodup ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra ∧
    destination.entry.allocation.extra.nodes.size+1 < 65536 ∧
    destination.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have room : input.contract.tracker.global.nextPointerTag.value < 18446744073709551615 := by
    simpa only [←referenceTracker] using fresh
  have destinationTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩ := by
    exact Option.some.inj destination.enabled.symm
  have member : (input.contract.destination.id,input.contract.destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.contract.destination.live)
  have nodes := input.contract.resources.nodeRoom
    (input.contract.destination.id,input.contract.destination.entry) member
  have afterRuntime := runtime_after_argument_registration input room
  have order := input.contract.runtime.parentTags
    (input.contract.destination.id,input.contract.destination.entry) member
  have roots := input.contract.runtime.roots
    (input.contract.destination.id,input.contract.destination.entry) member
  have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag fresh
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [entry,destinationTracker]
    simpa only [←referenceTracker] using afterRuntime
  · rw [entry]
    exact roots
  · rw [entry]
    exact order
  · rw [entry]
    dsimp only at nodes
    omega
  · rw [destinationTracker]
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
    have tags : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by
      simpa only [←referenceTracker] using input.contract.resources.tagRoom
    omega

/-- Fixed configuration facts survive the actual raw push and positive
argument FnEntry state update. The model is retimed for the return-place
tail's configuration at `remaining+1`. -/
theorem model_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    {id : AllocId} {tag : BorTag} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixCallModel.Model options (remaining+1) span
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry tag reference.offset len) := by
  have shifted := S03IntegerZeroState.retime input.contract.model (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := shifted.defaultTracker
  have same : tracker = reference.tracker := Option.some.inj (enabled.symm.trans reference.enabled)
  subst tracker
  refine {shifted with
    defaultTracker := ⟨⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,
      reference.tracker.retagMode⟩,rfl,mode⟩,
    unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact shifted.noGc

end
end DuplicatePrefix.S02SeparateDestinationReady

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SeparateDestinationReady.runtime_after_argument_registration,
      ``DuplicatePrefix.S02SeparateDestinationReady.local_facts_after_argument,
      ``DuplicatePrefix.S02SeparateDestinationReady.model_after_argument] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "{name} depends on unapproved axiom {ax}"
