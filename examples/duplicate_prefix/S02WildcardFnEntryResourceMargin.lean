import duplicate_prefix.S05WildcardEntryBridge

namespace DuplicatePrefix.S02WildcardFnEntryResourceMargin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- A real wildcard FnEntry consumes one tag and at most one physical slot;
the initial sixteen-slot budget therefore retains fifteen slots. This covers
both allocator append and coherent free-slot reuse, without supplying an
operation outcome or an intermediate margin as an input. -/
theorem after_wildcard
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : LegacyContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output),
      GeneralBorrowRawWildcardFnEntryRuntime.operation reference.entry.allocation.extra reference.tracker.global
        ({} : FrameState) reference.id reference.offset len = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = reference.entry.allocation.extra.locations.size ∧
      output.child.tree.nodes.size + 15 < 65536 ∧
      output.global.nextPointerTag.value.toNat + 15 < 2^64 ∧
      output.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 1 := by
  cases input.reference with
  | empty zero metadata => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    have same := DuplicatePrefixSliceArgument.Argument.pointer.inj encoding
    subst pointer
    have trackerEq : reference.tracker = input.tracker :=
      Option.some.inj (reference.enabled.symm.trans input.runtime.enabled)
    have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
    have nodeRoom := input.resources.nodeRoom (reference.id,reference.entry) member
    have tagRoom := input.resources.tagRoom
    rw [←trackerEq] at tagRoom
    obtain ⟨source,selected,maximum,positive,runtime,distinct,short,nodes,tags⟩ :=
      S05WildcardEntryBridge.from_positive address len reference input.runtime input.resources
    obtain ⟨output,actual,outputTag,global,frame,read,child,nextRuntime,capacity,growth,rest⟩ :=
      GeneralBorrowRawWildcardFnEntryResources.invoke reference.entry.allocation.extra reference.tracker.global
        ({} : FrameState) reference.id runtime reference.offset len positive distinct short nodes tags
    have counter : output.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 1 := by
      rw [global]
      change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag tags).value.toNat = _
      exact GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag tags
    refine ⟨reference,output,actual,read,child,nextRuntime,capacity,?_,?_,counter⟩
    · dsimp only at nodeRoom
      omega
    · omega

end
end DuplicatePrefix.S02WildcardFnEntryResourceMargin
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardFnEntryResourceMargin.after_wildcard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
