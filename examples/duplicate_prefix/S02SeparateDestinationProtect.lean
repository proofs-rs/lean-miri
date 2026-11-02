import duplicate_prefix.S02SeparateDestinationReady

namespace DuplicatePrefix.S02SeparateDestinationProtect
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Once the actual positive concrete argument has been installed, the
distinct concrete return allocation's real protection and uninitializing
write succeed from the original contract. The post-argument destination Input
is obtained by the earlier transport theorem; no future operation result is
assumed. This is the return-protection portion of initStackFrame, before the
final frame-state assignment. -/
theorem concrete_after_argument
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (budget : Nat) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
        reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks
          (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      ∃ after,
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          budget place (Storage.withCurrent #[] changed current) = .ok () after := by
  obtain ⟨reference,firstFresh,argument,destination,destId,destEntry,destOffset⟩ :=
    S02SeparateDestinationAuthorization.destination_input_after_argument
      id tag address len count input nonempty different
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  have frameBorrow : changed.extra.borrowTracker =
      some (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag) := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    rw [same,destId]
    exact returnConcrete
  obtain ⟨updated,actual,_,_,_,_,_,_,_,_⟩ := S03ReturnProtectionRaw.invoke_concrete
    (options := options) (remaining := remaining+1) (span := span)
    budget current model place destination runtime roots order nodes secondFresh returnTag concrete
    #[] changed (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
    frameBorrow #[] extras (by simp)
  exact ⟨reference,firstFresh,argument,_,actual⟩

end
end DuplicatePrefix.S02SeparateDestinationProtect

open Lean Elab Command in
run_cmd do
  let name := ``DuplicatePrefix.S02SeparateDestinationProtect.concrete_after_argument
  for ax in (← collectAxioms name) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "{name} depends on unapproved axiom {ax}"
