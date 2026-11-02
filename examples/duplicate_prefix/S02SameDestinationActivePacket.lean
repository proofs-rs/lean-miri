import duplicate_prefix.S02SameDestinationBorrowPacket
import duplicate_prefix.S02SameDestinationSourceParent
import duplicate_prefix.S02ProtectUninitOldActivity

namespace DuplicatePrefix.S02SameDestinationActivePacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact same-allocation installed packet additionally carries the
source's true bytewise activity after return protection and uninit. All fields
share one actual call-init witness and follow from the original contract. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset)))
        len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (updated : Allocation Provenance BorrowTree) (sourceChild returnChild : UniIndex)
        (sourceRaw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
        (sourceBefore sourceNode returnNode : TreeNode) (returnParent : UniIndex),
        let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
        let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag
        let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
          (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
        let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
          false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
        destination.id = reference.id ∧ destination.offset = input.contract.destination.offset ∧
        destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧
        destination.entry.allocation.extra.nodeAt sourceChild = some sourceBefore ∧ sourceBefore.tag = reference.tracker.global.nextPointerTag ∧
        sourceBefore.children = #[] ∧ sourceBefore.isExposed = false ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra sourceChild .Write reference.offset (reference.offset+len) ∧
        written.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧ written.nodeAt sourceChild = some sourceNode ∧
        sourceNode.tag = reference.tracker.global.nextPointerTag ∧ sourceNode.isExposed = false ∧
        written.nodeAt returnChild = some returnNode ∧ returnNode.tag = destination.tracker.global.nextPointerTag ∧
        returnNode.children = #[] ∧ returnNode.isExposed = false ∧
        destination.source = some returnParent ∧ returnNode.parent = some returnParent ∧ sourceChild ≠ returnChild ∧
        written.roots.toList.Nodup ∧ written.nodes.size < 65536 ∧
        updated.extra = written ∧ updated.byteSize = destination.entry.allocation.byteSize ∧ updated.len = destination.entry.allocation.len ∧
        updated.mutability = .Mut ∧
        DuplicatePrefixBorrowContract.RuntimeFacts written global ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len) ∧
        written.indexOfTag destination.tracker.global.nextPointerTag = some returnChild ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some returnChild) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written returnChild .Write destination.offset (destination.offset+1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written sourceChild .Write reference.offset (reference.offset+len) := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,sourceChild,returnChild,sourceRaw,sourceBefore,sourceNode,returnNode,returnParent,
      actual,sameId,destOffset,beforeTagged,beforePresent,beforeTag,beforeLeaf,beforeHidden,beforeActivity,
      sourceTagged,sourcePresent,sourceTag,sourceHidden,returnPresent,returnSame,returnLeaf,returnHidden,
      returnSource,returnEdge,differentChildren,rootsAfter,shortAfter,extra,bytes,length,mutable,post,postOrder,
      sourcePositive,returnTagged,returnPositive,returnActive⟩ :=
    S02SameDestinationBorrowPacket.enters id tag address len count input nonempty sameAllocation returnTag returnConcrete
  obtain ⟨_sourceChild,_raw,referenceId,_parent,_offset,_len,sourceLive,_enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have destEntry : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra (GeneralBorrowRawFnEntryArgument.finalTree
      reference.entry.allocation.extra reference.tracker tag reference.offset len)} := by
    have live := destination.live
    rw [sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans sourceLive))
  obtain ⟨runtime,roots,order,nodes,_fresh⟩ := S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have prov := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at prov
    have destIdEq : destination.id = input.contract.destination.id := sameId.trans (referenceId.trans sameAllocation)
    rw [Option.some.inj prov,destIdEq]
    exact returnConcrete
  obtain ⟨parent,parentSource,parentTagged,differentParent⟩ := S02SameDestinationSourceParent.separate id tag address len input sameAllocation
    reference firstFresh destination returnTag returnConcrete sourceChild sourceBefore beforePresent beforeTag
  obtain ⟨raw,rawParent,rawOffset,rawLength,_selected,_maximum⟩ :=
    S03ReturnProtectionRaw.packet destination runtime roots order nodes secondFresh returnTag concrete
  have parentEq : parent = raw.parent := by
    have tagged := raw.tagged
    rw [rawParent] at tagged
    exact Option.some.inj (parentTagged.symm.trans tagged)
  have different : sourceChild ≠ raw.parent := by simpa only [parentEq] using differentParent
  have active := S02ProtectUninitOldActivity.preserved destination.entry.allocation.extra destination.tracker ({} : FrameState) destination.id
    runtime raw sourceChild sourceBefore beforePresent beforeLeaf beforeHidden different reference.offset (reference.offset+len) beforeActivity
  simp only [rawParent,rawOffset,rawLength] at active
  exact ⟨reference,firstFresh,destination,secondFresh,updated,sourceChild,returnChild,sourceRaw,sourceBefore,sourceNode,returnNode,returnParent,
    actual,sameId,destOffset,beforeTagged,beforePresent,beforeTag,beforeLeaf,beforeHidden,beforeActivity,
    sourceTagged,sourcePresent,sourceTag,sourceHidden,returnPresent,returnSame,returnLeaf,returnHidden,
    returnSource,returnEdge,differentChildren,rootsAfter,shortAfter,extra,bytes,length,mutable,post,postOrder,
    sourcePositive,returnTagged,returnPositive,returnActive,active⟩

end
end DuplicatePrefix.S02SameDestinationActivePacket

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationActivePacket.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
