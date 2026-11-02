import duplicate_prefix.S05ConcreteEntryBridge

namespace DuplicatePrefix.S02FnEntryResourceMargin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The initial sixteen-slot budget leaves fifteen slots after the real
concrete FnEntry operation. The constructor and its resource consumption are
derived together from the call contract, with no intermediate fuel, operation
success, or remaining-margin premise. -/
theorem after_concrete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : Contract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
      (output : GeneralBorrowForestFnEntry.Output),
      reference.id = id ∧ raw.parentTag = tag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      GeneralBorrowForestFnEntry.operation reference.entry.allocation.extra reference.tracker.global
        ({} : FrameState) reference.id tag reference.offset len .VisitChildrenOfAccessed = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = reference.entry.allocation.extra.locations.size ∧
      output.child.tree.nodes.size + 15 < 65536 ∧
      output.global.nextPointerTag.value.toNat + 15 < 2^64 ∧
      output.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 1 := by
  obtain ⟨reference,sameId,raw,parentTag,offsetEq,lenEq,_,_,_,runtime⟩ :=
    S05ConcreteEntryBridge.from_contract id tag address len input nonempty
  have trackerEq : reference.tracker = input.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.runtime.enabled)
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have nodeRoom := input.resources.nodeRoom (reference.id,reference.entry) member
  have tagRoom := input.resources.tagRoom
  rw [←trackerEq] at tagRoom
  obtain ⟨output,actual,outputTag,global,frame,read,child,nextRuntime,capacity,growth,rest⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id runtime raw
  have counter : output.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 1 := by
    rw [global]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag raw.tagRoom).value.toNat = _
    exact GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag raw.tagRoom
  refine ⟨reference,raw,output,sameId.symm,parentTag,offsetEq,lenEq,?_,read,child,nextRuntime,capacity,?_,?_,counter⟩
  · simpa only [parentTag,offsetEq,lenEq] using actual
  · dsimp only at nodeRoom
    omega
  · omega

end
end DuplicatePrefix.S02FnEntryResourceMargin
open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02FnEntryResourceMargin.after_concrete) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
