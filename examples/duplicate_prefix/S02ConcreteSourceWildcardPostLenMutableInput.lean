import duplicate_prefix.S02ConcreteSourceWildcardSharedLenFullPacket
import duplicate_prefix.S02PostLenMutableInput

namespace DuplicatePrefix.S02ConcreteSourceWildcardPostLenMutableInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The actual wildcard-return source graph and the original resource margin
provide the mutable parent input after shared Ref/len. This is the input for
as_mut_ptr, not an assumption that the helper succeeds. -/
theorem from_contract
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
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourcePacket : S02ConcreteSourceWildcardBothPacket.SourcePacket id tag address len reference machine)
    (finalTree : BorrowTree) (held : MachineHooks.BorrowState)
    (raw : GeneralBorrowRawShared.Input
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len)
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag).global)
    (rawTag : raw.parentTag = reference.tracker.global.nextPointerTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global)
    (both : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
        reference.tracker tag reference.offset len)
      finalTree raw.selected
      (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) held) :
    ∃ mutableRaw : GeneralBorrowRawFnEntry.Input finalTree held.global,
      mutableRaw.parentTag = raw.parentTag ∧ mutableRaw.parent = raw.parent ∧
      mutableRaw.selected = raw.selected ∧ mutableRaw.maximum = raw.maximum ∧
      mutableRaw.offset = raw.offset ∧ mutableRaw.len = raw.len := by
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have referenceTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have destinationTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans (show
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len).borrowTracker =
      some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ from rfl))
  have firstStep := GenericFunctionEntryNumerics.successor_value
    reference.tracker.global.nextPointerTag firstFresh
  have secondStep := GenericFunctionEntryNumerics.successor_value
    destination.tracker.global.nextPointerTag secondFresh
  have initialCounter : tracker.global.nextPointerTag.value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 2 := by
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 1 at firstStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat =
      destination.tracker.global.nextPointerTag.value.toNat + 1 at secondStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = _
    rw [secondStep,destinationTracker]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat + 1 = _
    omega
  have tagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have margin := input.contract.resources.tagRoom
    have growth := graph.tagCounter
    change held.global.nextPointerTag.value.toNat =
      tracker.global.nextPointerTag.value.toNat + 2 at growth
    rw [referenceTracker] at initialCounter
    omega
  have sourceTagged : sourceTree.indexOfTag raw.parentTag = some raw.parent := raw.tagged
  have sameParent : raw.parent = sourcePacket.child := by
    rw [rawTag] at sourceTagged
    exact Option.some.inj (sourceTagged.symm.trans sourcePacket.tagged)
  have oldPresent : sourceTree.nodeAt raw.parent = some sourcePacket.node := by
    rw [sameParent]
    exact sourcePacket.present
  have oldTag : sourcePacket.node.tag = raw.parentTag := sourcePacket.same.trans rawTag.symm
  exact S02PostLenMutableInput.from_graph sourceTree finalTree tracker held raw runtime
    sourcePacket.node oldPresent oldTag both graph tagRoom

end
end DuplicatePrefix.S02ConcreteSourceWildcardPostLenMutableInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardPostLenMutableInput.from_contract) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard post-len mutable input dependency {dependency}"
