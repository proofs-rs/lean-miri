import duplicate_prefix.S02SeparateDestinationBothPhysicalInstalled
import duplicate_prefix.S02SeparateDestinationEntryIdentity
import duplicate_prefix.S02SeparateDestinationWrittenReady
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationPhysicalInstalled
import duplicate_prefix.S02SeparateDestinationPacketJoin
import duplicate_prefix.S02SeparateDestinationSourceFullAtWitness
import duplicate_prefix.S02SeparateDestinationSourceAbsent
import duplicate_prefix.S02SeparateDestinationHiddenFrame
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02SeparateDestinationReturnChild
import duplicate_prefix.S02SeparateDestinationReady
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02SeparateDestinationBothPhysicalReadyInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-- Actual installed call state retains the concrete return child packet
produced by the real post-argument protection and uninit write. -/
theorem enters_ready
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
        let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len
        let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
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
          S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame ∧
          ∃ (sourceChild : UniIndex) (sourceNode : TreeNode)
            (sourceRaw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
            (sourceTracker : MachineHooks.BorrowState),
            after.machine.borrowTracker = some sourceTracker ∧
            after.machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
            sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧
            sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode ∧
            sourceNode.tag = reference.tracker.global.nextPointerTag ∧ sourceNode.isExposed = false ∧
            DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra sourceTracker.global ∧
            Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
              sourceTracker.global.protectedTags (some sourceChild) (some sourceRaw.selected)
              sourceRaw.maximum reference.offset len) ∧
            GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
              reference.offset (reference.offset+len) ∧
            sourceEntry.allocation.extra.roots.toList.Nodup ∧
            (∀ valid : 0 < sourceEntry.allocation.extra.roots.size,
              sourceRaw.selected ≠ sourceEntry.allocation.extra.roots[0] →
                GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra) ∧
            sourceEntry.allocation.extra.nodes.size < 65536 ∧
            Nonempty (S03FinalReturnInputBounds.Destination after.machine place) ∧
            updated.extra.roots.toList.Nodup ∧
            GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra ∧
            updated.extra.nodes.size < 65536 := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,extra,tagged,runtime,
      positive,active,parent,node,parentTagged,present,same,edge,leaf,hidden,hiddenFrame,
      sourceChild,sourceNode,sourceRaw,sourceTracker,sourceEnabled,sourceLive,sourceTagged,
      sourcePresent,sourceSame,sourceHidden,sourceRuntime,sourcePositive,sourceActive,sourceRoots,
      sourceOrder,sourceShort,⟨physical⟩⟩ :=
    S02SeparateDestinationBothPhysicalInstalled.enters_both_physical id tag address len count input
      nonempty different returnTag returnConcrete
  obtain ⟨sameId,destId,destEntry,concrete⟩ :=
    S02SeparateDestinationEntryIdentity.from_contract id tag address len input reference firstFresh destination
      different returnTag returnConcrete
  obtain ⟨currentRuntime,roots,order,headroom,_fresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have writtenReady := S02SeparateDestinationWrittenReady.run destination currentRuntime roots order headroom
    secondFresh returnTag concrete
  have updatedReady : updated.extra.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra ∧
      updated.extra.nodes.size < 65536 := by
    rw [extra]
    exact writtenReady
  exact ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,extra,tagged,runtime,
      positive,active,parent,node,parentTagged,present,same,edge,leaf,hidden,hiddenFrame,
      sourceChild,sourceNode,sourceRaw,sourceTracker,sourceEnabled,sourceLive,sourceTagged,
      sourcePresent,sourceSame,sourceHidden,sourceRuntime,sourcePositive,sourceActive,sourceRoots,
      sourceOrder,sourceShort,⟨physical⟩,updatedReady.1,updatedReady.2.1,updatedReady.2.2⟩

end
end DuplicatePrefix.S02SeparateDestinationBothPhysicalReadyInstalled

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationBothPhysicalReadyInstalled.enters_ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination both-ready dependency {dependency}"
