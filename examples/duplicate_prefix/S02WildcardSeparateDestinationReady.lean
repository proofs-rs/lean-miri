import duplicate_prefix.S02WildcardSeparateDestinationInput
import duplicate_prefix.S02SeparateDestinationReady

namespace DuplicatePrefix.S02WildcardSeparateDestinationReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Runtime, root-order and resource facts for the original destination on
the exact positive wildcard post-argument machine in the separate-allocation
branch. No return operation is assumed. -/
theorem local_facts_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry output.child.tree) place)
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
  have afterRuntime := S02SeparateDestinationReady.runtime_after_argument_registration input room
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

/-- The fixed model retimes through the wildcard argument update because
that update changes borrow state and memory, not the user control flags. -/
theorem model_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixCallModel.Model options (remaining+1) span
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker fresh reference.id reference.entry output.child.tree) := by
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
end DuplicatePrefix.S02WildcardSeparateDestinationReady

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02WildcardSeparateDestinationReady.local_facts_after_argument,
      ``DuplicatePrefix.S02WildcardSeparateDestinationReady.model_after_argument] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
