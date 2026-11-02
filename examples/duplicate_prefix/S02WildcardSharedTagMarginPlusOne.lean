import duplicate_prefix.S02WildcardSeparateDestinationReady

namespace DuplicatePrefix.S02WildcardSharedTagMarginPlusOne
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The contract's tag reserve leaves an additional successor margin for the
shared Ref and subsequent length-call helper. -/
theorem after_second_protector_plus_one
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} {address len : UInt64}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry output.child.tree) place)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615) :
    (TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag).nextPointerTag.value.toNat + 1 < 18446744073709551615 := by
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have destinationTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ := by
    exact Option.some.inj destination.enabled.symm
  have firstSuccessor := GenericFunctionEntryNumerics.successor_value
    reference.tracker.global.nextPointerTag firstFresh
  have secondSuccessor := GenericFunctionEntryNumerics.successor_value
    destination.tracker.global.nextPointerTag secondFresh
  have originalRoom : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by
    simpa only [←referenceTracker] using input.contract.resources.tagRoom
  have destinationValue : destination.tracker.global.nextPointerTag.value.toNat =
      (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat := by
    exact congrArg (fun tracker : MachineHooks.BorrowState =>
      tracker.global.nextPointerTag.value.toNat) destinationTracker
  change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat + 1 <
    18446744073709551615
  omega

end
end DuplicatePrefix.S02WildcardSharedTagMarginPlusOne

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSharedTagMarginPlusOne.after_second_protector_plus_one) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard shared-tag plus-one dependency {dependency}"
