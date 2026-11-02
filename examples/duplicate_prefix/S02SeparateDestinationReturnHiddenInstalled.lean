import duplicate_prefix.S02SeparateDestinationReturnLiteralInstalled
import duplicate_prefix.S02SeparateDestinationSourceAbsent
import duplicate_prefix.S02SeparateDestinationHiddenFrame
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02SeparateDestinationReturnChild
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02SeparateDestinationReturnHiddenInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-- Actual installed call state retains the concrete return child packet
produced by the real post-argument protection and uninit write. -/
theorem enters_hidden
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let rawMachine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine rawMachine reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (updated : Allocation Provenance BorrowTree) (child : UniIndex),
        let frame := (RootArgumentsTwo.result
          (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
            reference.id reference.tracker.global.nextPointerTag) count).frame
        let changed := {frame with location := .unwinding ⟨601⟩}
        let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
        let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
          destination.tracker returnTag destination.offset 1
        let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
          (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
          (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
            destination.tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
          destination.tracker.global.nextPointerTag
        let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
        let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
        let global := TypedBorrowSteps.registeredGlobal
          (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
        updated.extra = written ∧
        updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child ∧
        DuplicatePrefixBorrowContract.RuntimeFacts updated.extra global ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra global.protectedTags
          (some child) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write
          destination.offset (destination.offset+1) ∧
        ∃ parent node, updated.extra.indexOfTag returnTag = some parent ∧
          updated.extra.nodeAt child = some node ∧
          node.tag = destination.tracker.global.nextPointerTag ∧
          node.parent = some parent ∧ node.children = #[] ∧ node.isExposed = false ∧
          S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,extra,tagged,runtime,
      positive,active,parent,node,parentTagged,present,same,edge,leaf,hidden⟩ :=
    S02SeparateDestinationReturnLiteralInstalled.enters_literal id tag address len count input nonempty different
      returnTag returnConcrete
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  have idEq : id = reference.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1
  have destId : destination.id = input.contract.destination.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by simpa only [←destId,←idEq] using different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory reference.id
        reference.entry (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len)).live.find? (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  have sourceAbsent := S02SeparateDestinationSourceAbsent.written id tag address len input reference
    firstFresh destination destEntry secondFresh returnTag concrete
  have sourceAbsentUpdated : updated.extra.indexOfTag reference.tracker.global.nextPointerTag = none := by
    rw [extra]
    exact sourceAbsent
  have ownedTags : borrowFrame.protectedTags =
      #[(reference.id,reference.tracker.global.nextPointerTag),
        (destination.id,destination.tracker.global.nextPointerTag)] := by
    simp [borrowFrame,owned,FrameState.addProtector]
  have hiddenFrame := S02SeparateDestinationHiddenFrame.of_absent updated.extra
    (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag)
    borrowFrame reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag child node ownedTags runtime sourceAbsentUpdated tagged present hidden
  exact ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,extra,tagged,runtime,
    positive,active,parent,node,parentTagged,present,same,edge,leaf,hidden,hiddenFrame⟩

end
end DuplicatePrefix.S02SeparateDestinationReturnHiddenInstalled

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationReturnHiddenInstalled.enters_hidden) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination return hidden installed dependency {dependency}"
