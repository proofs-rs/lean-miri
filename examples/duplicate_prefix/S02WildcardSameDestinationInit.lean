import duplicate_prefix.S02WildcardSameDestinationInitAfterArgument
import duplicate_prefix.S02WildcardSameDestinationCoreProtect
import duplicate_prefix.S02WildcardFinishFromProtect
namespace DuplicatePrefix.S02WildcardSameDestinationInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real positive wildcard call initializes its concrete return place in
the same resolved allocation. One exact installed witness carries the source
and destination packet used by the unchanged zero-count body. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len) (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) = .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      (reference.id = input.contract.destination.id →
        ∃ (data : S02WildcardSameDestinationInitAfterArgument.Ready input reference output fresh returnTag)
          (updated : Allocation Provenance BorrowTree),
          let destination := data.destination
          let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
          let after := S04ProtectUninit.finished current place destination #[] changed owned data.nextFresh tree updated
          let installed := CallEntryFacts.doneRootFrame
            {TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
          TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place
            (Storage.withCurrent #[] changed current) = .ok () after ∧
          Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
            RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
            #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
              (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
            false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
          Nonempty (S02SameDestinationZeroCore.Packet installed after.machine place)) := by
  obtain ⟨reference,output,fresh,_run,argument,ready⟩ :=
    S02WildcardSameDestinationInitAfterArgument.ready address len count input nonempty returnTag returnConcrete
  refine ⟨reference,output,fresh,argument,?_⟩
  intro same
  obtain ⟨data⟩ := ready same
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let destination := data.destination
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output fresh
  have destId : destination.id = input.contract.destination.id := data.sameId.trans same
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,#[]⟩) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,destId]
    exact input.return_extras
  have ownedSource : owned.protectedTags = #[(destination.id,reference.tracker.global.nextPointerTag)] := by
    rw [data.sameId]
    rfl
  obtain ⟨updated,protect,packet⟩ := S02WildcardSameDestinationCoreProtect.invoke
    (options := options) (remaining := remaining+1) (span := span) limits.retag current model place destination
    data.runtime data.distinct data.order data.headroom data.nextFresh returnTag data.concrete changed owned frameBorrow extras
    reference.tracker.global.nextPointerTag data.child data.child (some reference.tracker.global.nextPointerTag)
    reference.offset len data.node data.tagged data.present data.tag data.leaf data.hidden data.positive data.activity
    data.notSourceParent data.disjoint ownedSource
  have actual := S02WildcardFinishFromProtect.init address len count input nonempty reference output fresh argument destination
    data.nextFresh (GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1)
    updated protect
  exact ⟨data,updated,protect,actual,packet⟩
end
end DuplicatePrefix.S02WildcardSameDestinationInit
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationInit.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard same actual init dependency {dependency}"
