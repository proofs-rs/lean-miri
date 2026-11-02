import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S03ReturnTagFrame
import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.ConcreteEmptyRuntimeEntry

namespace DuplicatePrefix.S02SeparateDestinationSourceAbsent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The positive argument's fresh protector tag never belongs to a node of
the distinct return allocation, including after the real return-child Write. -/
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
    (returnTag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id returnTag) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
      destination.tracker returnTag destination.offset 1
    let global := TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag
    let result := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
      (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    result.indexOfTag reference.tracker.global.nextPointerTag = none := by
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
  obtain ⟨runtime,roots,order,headroom,_fresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination entryEq
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ :=
    S03ReturnProtectionRaw.packet destination runtime roots order headroom secondFresh returnTag concrete
  have oldTags := S03ReturnTagFrame.run destination.entry.allocation.extra destination.tracker
    ({} : FrameState) destination.id runtime raw
  simp only [parentTag,offset,length] at oldTags
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
end DuplicatePrefix.S02SeparateDestinationSourceAbsent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceAbsent.written) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-absent dependency {dependency}"
