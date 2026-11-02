import duplicate_prefix.S02WildcardSeparateConcreteProtectSource
import duplicate_prefix.S02WildcardFinishFromProtect
import duplicate_prefix.S02SeparateDestinationPhysical
import duplicate_prefix.S02SeparateDestinationWrittenShape
import duplicate_prefix.S02SeparateDestinationTransport
import duplicate_prefix.S02WildcardReturnHiddenCurrent

namespace DuplicatePrefix.S02WildcardBothInstalledFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact installed frame is the one built from the same wildcard source and
concrete return protector witnesses. -/
theorem installed
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      reference.id ≠ input.contract.destination.id →
        ∃ (frame : CompilerFrameContext.ActualFrame)
          (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
          (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
          (sourceChild : UniIndex) (sourceNode : TreeNode)
          (sourceTracker : MachineHooks.BorrowState),
          Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
            RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
            #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
              (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
              .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
            ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
          machine.borrowTracker = some sourceTracker ∧
          machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
          sourceEntry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild ∧
          sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode ∧
          sourceNode.tag = reference.tracker.global.nextPointerTag ∧ sourceNode.parent = none ∧
          sourceNode.children = #[] ∧ sourceNode.isExposed = false ∧
          DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra sourceTracker.global ∧
          Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
            sourceTracker.global.protectedTags (some sourceChild) (some sourceChild)
            (some reference.tracker.global.nextPointerTag) reference.offset len) ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
            reference.offset (reference.offset+len) ∧
          sourceEntry.allocation.extra.roots.toList.Nodup ∧
          GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra ∧
          sourceEntry.allocation.extra.nodes.size < 65536 ∧
          Nonempty (S03FinalReturnInputBounds.Destination machine place) ∧
          ∃ (destination : DuplicatePrefixReturnPlaceInput.Input
              (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
                (RawRootInvocation.machine #[] before) reference.tracker firstFresh
                reference.id reference.entry output.child.tree) place)
            (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
            (updated : Allocation Provenance BorrowTree) (returnChild : UniIndex),
            let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
              (RawRootInvocation.machine #[] before) reference.tracker firstFresh
              reference.id reference.entry output.child.tree
            let root := RawRootInvocation.root before place input.contract.model.noDataRace
            let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
                (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
            let argumentFrame := (RootArgumentsTwo.result
              (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
                reference.id reference.tracker.global.nextPointerTag) count).frame
            let changed := {argumentFrame with location := .unwinding ⟨601⟩}
            let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
            let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
              destination.tracker returnTag destination.offset 1
            let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
            let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
              destination.tracker.global.nextPointerTag
            let expectedFrame := CallEntryFacts.doneRootFrame
              {protectedFrame with location := .unwinding ⟨559⟩}
            let global := TypedBorrowSteps.registeredGlobal
              (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
              destination.tracker.global.nextPointerTag
            let written := (tree.performBorrowAccessRange
              (.concrete destination.tracker.global.nextPointerTag)
              (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write
              global.protectedTags .VisitChildrenOfAccessed).tree
            frame = expectedFrame ∧ machine = after.machine ∧
            updated.extra = written ∧
            updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some returnChild ∧
            DuplicatePrefixBorrowContract.RuntimeFacts updated.extra global ∧
            Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra global.protectedTags
              (some returnChild) destination.selectedRoot destination.maximum destination.offset 1) ∧
            GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra returnChild .Write
              destination.offset (destination.offset+1) ∧
            S04ReturnReleaseParent.HiddenFrame updated.extra
              (owned.addProtector destination.id destination.tracker.global.nextPointerTag) := by
  obtain ⟨reference,output,firstFresh,argument,ready⟩ :=
    S02WildcardSeparateConcreteProtectSource.source_after_protect address len count input nonempty
      returnTag returnConcrete
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine rawMachine reference.tracker firstFresh
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
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  refine ⟨reference,output,firstFresh,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,sourceChild,sourceNode,sourceTracker,
    protect,tracked,sourceLive,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort⟩ := ready different
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have destId : destination.id = input.contract.destination.id := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by rw [destId];exact different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory rawMachine.memory reference.id reference.entry output.child.tree).live.find?
        (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨secondFresh2,updated2,returnChild,protect2,extra,returnTagged,returnRuntime,
    returnPositive,returnActivity,returnHidden,physical2⟩ :=
    S02WildcardReturnHiddenCurrent.current address len count input reference output firstFresh
      destination destEntry returnTag concrete
  let tree2 := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after2 := S04ProtectUninit.finished current place destination #[] changed owned secondFresh2 tree2 updated2
  have stateEq : after = S04ProtectUninit.finished current place destination #[] changed owned
      secondFresh2 tree2 updated2 := (EStateM.Result.ok.inj (protect.symm.trans protect2)).2
  have actual2 := S02WildcardFinishFromProtect.init address len count input nonempty
    reference output firstFresh argument destination secondFresh2 tree2 updated2 protect2
  have tracked2 : after2.machine.borrowTracker = some sourceTracker := by
    change (S04ProtectUninit.finished current place destination #[] changed owned secondFresh2 tree2 updated2).machine.borrowTracker = _
    rw [← stateEq]
    exact tracked
  have sourceLive2 : after2.machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    change (S04ProtectUninit.finished current place destination #[] changed owned secondFresh2 tree2 updated2).machine.memory.live.find? (fun row => row.1 == reference.id) = _
    rw [← stateEq]
    exact sourceLive
  exact ⟨installed,after2.machine,sourceEntry,sourceChild,sourceNode,sourceTracker,
    actual2,tracked2,sourceLive2,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort,physical2,
    destination,secondFresh2,updated2,returnChild,rfl,rfl,extra,returnTagged,returnRuntime,
    returnPositive,returnActivity,returnHidden⟩

end
end DuplicatePrefix.S02WildcardBothInstalledFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardBothInstalledFrame.installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard both-installed frame dependency {dependency}"
