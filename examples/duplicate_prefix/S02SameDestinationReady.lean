import duplicate_prefix.S02SameDestinationInput
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.GeneralBorrowRawFnEntryOrder

namespace DuplicatePrefix.S02SameDestinationReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Runtime, full parent order and residual resources for protection of the
same-allocation destination after actual argument FnEntry. The source's consumed
node/tag budget is accounted for from the original call resources. -/
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
    (entry : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len)}) :
    DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global ∧
    destination.entry.allocation.extra.roots.toList.Nodup ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra ∧
    destination.entry.allocation.extra.nodes.size+1 < 65536 ∧
    destination.tracker.global.nextPointerTag.value < 18446744073709551615 := by
  obtain ⟨_id,raw,parentTag,offsetEq,lenEq,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
  have facts := GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker ({} : FrameState)
    reference.id runtime raw
  obtain ⟨nextRuntime,capacity,growth,roots,_held,_frame,_fresh,_rest⟩ := facts
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have initialOrder := input.contract.runtime.parentTags (reference.id,reference.entry) member
  have nextOrder := GeneralBorrowRawFnEntryOrder.order reference.entry.allocation.extra reference.tracker ({} : FrameState)
    reference.id runtime raw initialOrder
  simp only [parentTag,offsetEq,lenEq] at nextRuntime capacity growth roots nextOrder
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len
  have destinationTree : destination.entry.allocation.extra = finalTree := by rw [entry];rfl
  have destinationTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have nodes := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have initialRoots := input.contract.runtime.roots (reference.id,reference.entry) member
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag fresh
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [destinationTree,destinationTracker]
    exact nextRuntime
  · rw [destinationTree,roots]
    exact initialRoots
  · rw [destinationTree]
    exact nextOrder
  · rw [destinationTree]
    dsimp only at nodes growth
    dsimp only [finalTree]
    omega
  · rw [destinationTracker]
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
    have tags : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by
      simpa only [←referenceTracker] using input.contract.resources.tagRoom
    omega

end
end DuplicatePrefix.S02SameDestinationReady

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationReady.local_facts_after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
