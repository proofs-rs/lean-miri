import duplicate_prefix.S02WildcardReturnMetadataCurrent
import duplicate_prefix.S02WildcardSeparateConcreteHiddenFrame

namespace DuplicatePrefix.S02WildcardReturnHiddenCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual wildcard-source, concrete-return protector creates the exact
hidden destination child with full return write permission. -/
theorem current
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
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
    (entryEq : destination.entry = input.contract.destination.entry)
    (returnTag : BorTag) (concrete : destination.pointer.provenance = .concrete destination.id returnTag) :
    let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
      (RawRootInvocation.machine #[] before) reference.tracker firstFresh
      reference.id reference.entry output.child.tree
    let root := RawRootInvocation.root before place input.contract.model.noDataRace
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
    let frame := (RootArgumentsTwo.result
      (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) count).frame
    let changed := {frame with location := .unwinding ⟨601⟩}
    let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
    ∃ (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (updated : Allocation Provenance BorrowTree) (child : UniIndex),
      let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
        destination.tracker returnTag destination.offset 1
      let global := TypedBorrowSteps.registeredGlobal
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag
      let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
        (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
        global.protectedTags .VisitChildrenOfAccessed).tree
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
        limits.retag place (Storage.withCurrent #[] changed current) = .ok () after ∧
      updated.extra = written ∧
      updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra global.protectedTags
        (some child) destination.selectedRoot destination.maximum destination.offset 1) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write
        destination.offset (destination.offset+1) ∧
      S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame ∧
      Nonempty (S03FinalReturnInputBounds.Destination after.machine place) := by
  obtain ⟨secondFresh,updated,protect,extra,runtime,⟨child,lookup,positive,active⟩,physical⟩ :=
    S02WildcardReturnMetadataCurrent.current address len count input reference output firstFresh
      destination entryEq returnTag concrete
  obtain ⟨_runtime,parent,hiddenChild,node,parentTag,childTag,present,tag,edge,leaf,hidden,hiddenFrame⟩ :=
    S02WildcardSeparateConcreteHiddenFrame.written_hidden address len input reference output
      firstFresh destination entryEq secondFresh returnTag concrete
  have same : child = hiddenChild := Option.some.inj (lookup.symm.trans childTag)
  subst hiddenChild
  have runtimeCurrent : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra
      (TypedBorrowSteps.registeredGlobal
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := by
    rw [extra]
    exact runtime
  have positiveCurrent : Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra
      (TypedBorrowSteps.registeredGlobal
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag).protectedTags
      (some child) destination.selectedRoot destination.maximum destination.offset 1) := by
    rw [extra]
    exact positive
  have activeCurrent : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write
      destination.offset (destination.offset+1) := by
    rw [extra]
    exact active
  have hiddenCurrent : S04ReturnReleaseParent.HiddenFrame updated.extra
      ((({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag).addProtector
        destination.id destination.tracker.global.nextPointerTag) := by
    rw [extra]
    exact hiddenFrame
  have lookupCurrent : updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child := by
    rw [extra]
    exact lookup
  exact ⟨secondFresh,updated,child,protect,extra,lookupCurrent,runtimeCurrent,
    positiveCurrent,activeCurrent,hiddenCurrent,physical⟩

end
end DuplicatePrefix.S02WildcardReturnHiddenCurrent

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnHiddenCurrent.current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard hidden return dependency {dependency}"
