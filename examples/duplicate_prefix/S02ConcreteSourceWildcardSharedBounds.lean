import duplicate_prefix.S02ConcreteSourceWildcardControl
import duplicate_prefix.S02SeparateDestinationSharedBounds

namespace DuplicatePrefix.S02ConcreteSourceWildcardSharedBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Numeric and source-storage prerequisites of shared Ref/len at the actual
positive concrete-source, wildcard-return installed machine. -/
theorem at_installed
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
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615) :
    let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker tag reference.offset len
    let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
    let tracker := TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    (0 : UInt64) < len ∧ reference.base+reference.offset ≠ 0 ∧
    len.toNat < 9223372036854775808 ∧
    reference.offset.toNat + len.toNat ≤ sourceEntry.allocation.byteSize.bytes.toNat ∧
    sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
    sourceEntry.allocation.extra.nodes.size + 2 < 65536 ∧
    sourceEntry.allocation.extra.nodes.size + 2 ≤ 4294967295 ∧
    tracker.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 := by
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have destTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ := by
    exact Option.some.inj (destination.enabled.symm.trans (show
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len).borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ from rfl))
  have counter : tracker.global.nextPointerTag.value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 2 := by
    have firstStep := GenericFunctionEntryNumerics.successor_value
      reference.tracker.global.nextPointerTag firstFresh
    have secondStep := GenericFunctionEntryNumerics.successor_value
      destination.tracker.global.nextPointerTag secondFresh
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 1 at firstStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat =
      destination.tracker.global.nextPointerTag.value.toNat + 1 at secondStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = _
    rw [secondStep,destTracker]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat + 1 = _
    omega
  exact S02SeparateDestinationSharedBounds.of_exact_source id tag address len input reference
    sourceEntry rfl tracker counter

end
end DuplicatePrefix.S02ConcreteSourceWildcardSharedBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardSharedBounds.at_installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard shared-bounds dependency {dependency}"
