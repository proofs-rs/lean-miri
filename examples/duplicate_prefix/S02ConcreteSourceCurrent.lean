import duplicate_prefix.S02ConcreteSourceFormation
import duplicate_prefix.S05ConcreteEntryBridge

namespace DuplicatePrefix.S02ConcreteSourceCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The same positive reference that appears in the actual typed argument
result has a live source row whose installed tree has RuntimeFacts and full
Positive capability. The raw tree definition depends only on the borrow
tracker global, so its `.FnEntry` proof model and the actual reference's
`Default` mode give the identical installed tree. -/
theorem source_ready_at_actual_current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615) :
    let machine := RawRootInvocation.machine #[] before
    let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
      reference.id reference.entry tag reference.offset len
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len
    let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra finalTree}
    ∃ (child : UniIndex) (raw : GeneralBorrowRawFnEntry.Input
        reference.entry.allocation.extra reference.tracker.global),
      reference.id = id ∧ raw.parentTag = tag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      current.borrowTracker = some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,
        reference.tracker.retagMode⟩ ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra
        (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
        (some child) (some raw.selected) raw.maximum reference.offset len) := by
  obtain ⟨same,raw,parent,offset,length,_source,_selected,_maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference
      input.contract.runtime input.contract.resources
  obtain ⟨child,afterRuntime,_lookup,⟨afterPositive⟩⟩ :=
    S02ConcreteSourceFormation.exact_source_tree reference.entry.allocation.extra
      reference.tracker.global ({} : FrameState) reference.id runtime raw
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  have treeEq : finalTree = GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      (⟨reference.tracker.global,.FnEntry⟩ : MachineHooks.BorrowState)
      raw.parentTag raw.offset raw.len := by
    rw [parent,offset,length]
    rfl
  let machine := RawRootInvocation.machine #[] before
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra finalTree}
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry tag reference.offset len
  have rawLive : machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,reference.entry) := by
    rw [(RawRootInvocation.preservation #[] before).1]
    exact reference.live
  have noMatch : machine.memory.live.find? (fun _ => false) = none := by
    apply Array.find?_eq_none.mpr
    intro row member
    simp
  have live : current.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    simp only [current,GeneralBorrowRawFnEntryScope.resultMachine,RetagEntry.updatedMemory,
      Array.find?_push,Array.find?_filter]
    simp [sourceEntry,noMatch]
    rfl
  refine ⟨child,raw,same.symm,parent,offset,length,live,rfl,?_,?_⟩
  · rw [←treeEq] at afterRuntime
    change DuplicatePrefixBorrowContract.RuntimeFacts finalTree
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh)
    exact afterRuntime
  · rw [←treeEq] at afterPositive
    refine ⟨?_⟩
    change DuplicatePrefixBorrowAuthorization.Positive finalTree
      (TypedRetagGeneric.protectedGlobal reference.tracker.global fresh).protectedTags
      (some child) (some raw.selected) raw.maximum reference.offset len
    simpa only [offset,length] using afterPositive

end
end DuplicatePrefix.S02ConcreteSourceCurrent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceCurrent.source_ready_at_actual_current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete source current dependency {dependency}"
