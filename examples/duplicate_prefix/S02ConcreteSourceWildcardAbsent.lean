import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S03ReturnWildcardProtectionRawOtherTags
import duplicate_prefix.ConcreteEmptyRuntimeEntry

namespace DuplicatePrefix.S02ConcreteSourceWildcardAbsent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The actual wildcard destination constructor's old-tag frame makes the
positive concrete source protector absent from the distinct return tree. -/
theorem written
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
    (entryEq : destination.entry = input.contract.destination.entry)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (writtenTree : BorrowTree)
    (oldTags : ∀ query, destination.tracker.global.nextPointerTag ≠ query →
      writtenTree.indexOfTag query = destination.entry.allocation.extra.indexOfTag query) :
    writtenTree.indexOfTag reference.tracker.global.nextPointerTag = none := by
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have member : (input.contract.destination.id,input.contract.destination.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.contract.destination.live)
  have below := input.contract.resources.tagsBelow
    (input.contract.destination.id,input.contract.destination.entry) member
  have absent : destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = none := by
    rw [entryEq]
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [referenceTracker]
    rw [GeneralBorrowTagMap.fresh_find _ _
      (ConcreteEmptyRuntimeEntry.counter_fresh _ _ below)]
    rfl
  have destinationTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ := Option.some.inj destination.enabled.symm
  have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
  have different : destination.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag := by
    intro same
    have values := congrArg (fun value : BorTag => value.value.toNat) same
    rw [destinationTracker] at values
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat at values
    omega
  exact (oldTags reference.tracker.global.nextPointerTag different).trans absent

end
end DuplicatePrefix.S02ConcreteSourceWildcardAbsent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardAbsent.written) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard return source-absent dependency {dependency}"
