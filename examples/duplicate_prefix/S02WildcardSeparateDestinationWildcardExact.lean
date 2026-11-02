import duplicate_prefix.S02WildcardSeparateDestinationWildcardProtect
import duplicate_prefix.S03ReturnWildcardProtectionRaw
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02WildcardSeparateDestinationWildcardExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Exact return-protection post-state after the actual positive wildcard
argument, for a distinct wildcard destination allocation. The allocation update is the
real uninit write, and the original final frame step succeeds on that state.
The post-argument destination Input and all local resources are derived from
the original call contract. -/
theorem wildcard_after_argument_finish
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (budget : Nat) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
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
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks
          (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second count))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[] frame current) ∧
      (reference.id ≠ input.contract.destination.id →
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
        let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
        TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
          budget place (Storage.withCurrent #[] changed current) = .ok () after ∧
        updated.byteSize = destination.entry.allocation.byteSize ∧
        updated.len = destination.entry.allocation.len ∧
        updated.mutability = .Mut ∧
        ∃ final,
          RootEntryFinish.finish (ExecutionMachine.callHooks (config options (remaining+1) span) limits) after =
            .ok () final) := by
  obtain ⟨reference,output,firstFresh,run,argument,destinationReady⟩ :=
    S02WildcardSeparateDestinationInput.destination_input_after_argument
      address len count input nonempty
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
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
  refine ⟨reference,output,firstFresh,argument,?_⟩
  intro different
  obtain ⟨destination,destId,destEntry,_⟩ := destinationReady different
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,
      RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh destination destEntry
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    have preserved := (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
    rw [preserved]
    exact input.return_extras
  have wildcard : destination.pointer.provenance = .wildcard := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    rw [same]
    exact returnWildcard
  obtain ⟨tree,updated,actual,_,bytes,length,mutable,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ :=
    S03ReturnWildcardProtectionRaw.invoke
      (options := options) (remaining := remaining+1) (span := span)
      budget current model place destination runtime roots order nodes secondFresh wildcard
      #[] changed owned frameBorrow #[] extras (by simp)
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  have shape := S02PositiveFinishFrame.after_destination_registration root
    (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  obtain ⟨body,size,dead,noClocks⟩ := shape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine
    body size (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
    (dead ⟨6,by decide⟩ (by omega) (Or.inr (Or.inl rfl)))
    (dead ⟨13,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inl rfl))))
    (dead ⟨14,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inr rfl)))) noClocks
  refine ⟨destination,secondFresh,tree,updated,actual,bytes,length,mutable,?_⟩
  let final := Storage.withCurrent #[]
    (CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}) after.machine
  refine ⟨final,?_⟩
  change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) = .ok () final
  exact finish

end
end DuplicatePrefix.S02WildcardSeparateDestinationWildcardExact

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateDestinationWildcardExact.wildcard_after_argument_finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard destination exact dependency {dependency}"
