import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02SeparateDestinationSourceReady

namespace DuplicatePrefix.S02SeparateDestinationSourceAtWitness
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Full Both permission on the positive source window survives the second
protector in the exact supplied witness. This is a state transport lemma;
the caller obtains the actual protection equation independently. -/
theorem source_positive
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
    (different : destination.id ≠ reference.id)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) :
    let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker firstFresh reference.id reference.entry tag reference.offset len
    let after := S04ProtectUninit.finished current place destination #[] frame borrowFrame secondFresh tree updated
    let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len
    let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
    ∃ (child : UniIndex) (raw : GeneralBorrowRawFnEntry.Input
        reference.entry.allocation.extra reference.tracker.global)
      (tracker : MachineHooks.BorrowState),
      after.machine.borrowTracker = some tracker ∧
      after.machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        tracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len) := by
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  obtain ⟨child,raw,same,parent,offset,length,sourceLive,enabled,runtime,⟨positive⟩⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have trackerEq : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have globalEq : destination.tracker.global =
      TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh :=
    congrArg MachineHooks.BorrowState.global trackerEq
  rw [←globalEq] at runtime positive
  obtain ⟨sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      frame borrowFrame secondFresh tree updated reference.id sourceEntry different sourceLive runtime
      (some child) (some raw.selected) raw.maximum reference.offset len positive
  exact ⟨child,raw,sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩

end
end DuplicatePrefix.S02SeparateDestinationSourceAtWitness

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceAtWitness.source_positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-witness dependency {dependency}"
