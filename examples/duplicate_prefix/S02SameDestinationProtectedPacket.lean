import duplicate_prefix.S02SameDestinationAuthorization
import duplicate_prefix.S02SameDestinationReady
import duplicate_prefix.S02SameAllocationProtectPacket
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02SameDestinationProtectedPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- One actual same-allocation call-init witness carries BOTH the original
source's full Positive and the return child's Positive/runtime/activity on the
exact written tree. No future state, operation success or borrow capability is
a caller premise. Source activity is a separate geometric transport. -/
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
        (sourceRaw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global),
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
        updated.extra = written ∧ updated.byteSize = destination.entry.allocation.byteSize ∧ updated.len = destination.entry.allocation.len ∧
        updated.mutability = .Mut ∧
        DuplicatePrefixBorrowContract.RuntimeFacts written global ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len) ∧
        written.indexOfTag destination.tracker.global.nextPointerTag = some returnChild ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some returnChild) destination.selectedRoot destination.maximum destination.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written returnChild .Write destination.offset (destination.offset+1) := by
  obtain ⟨reference,firstFresh,argument,destination,destId,destEntry,destOffset⟩ :=
    S02SameDestinationAuthorization.destination_input_after_argument id tag address len count input nonempty sameAllocation
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
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,frame,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  obtain ⟨runtime,roots,order,nodes,secondFresh⟩ := S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,#[]⟩) := by
    rw [destId]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2]
    exact input.return_extras
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨sourceChild,sourceRaw,sourceId,_parent,_offset,_length,_live,enabled,_runtime,⟨sourcePositive⟩⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have trackerEq : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra destination.tracker.global.protectedTags
      (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len := by
    rw [destEntry,trackerEq]
    exact sourcePositive
  have separation := S02SameDestinationLiveTransport.actual_reference_disjoint id tag address len input nonempty sameAllocation reference
  have stopEq : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt reference.borrow.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  have disjoint : destination.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destination.offset.toNat := by
    rw [destOffset,stopEq]
    exact separation.symm
  obtain ⟨updated,protect,extra,bytes,length,mutable,sourceAfter,post,postOrder,returnChild,tagged,returnPositive,active⟩ :=
    S02SameAllocationProtectPacket.invoke (options := options) (remaining := remaining+1) (span := span) limits.retag current model place destination
      runtime roots order nodes secondFresh returnTag concrete #[] changed owned frameBorrow #[] extras (by simp)
      (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len disjoint positive
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let done := Storage.withCurrent #[] (CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}) after.machine
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
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] frame current
    (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] frame current) = .ok () done := by
    unfold RootEntryTail.tail RootCallCore.spanAt
    simp only [bind,EStateM.bind]
    rw [localSpan]
    simp only [EStateM.bind]
    rw [getFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at setFrame
    rw [setFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at compat
    rw [compat]
    simp only [EStateM.bind,Bool.not_true,ite_false,pure,EStateM.pure]
    change (do
      TypedRetag.protectInPlaceFunctionArgument
        (config options (remaining+1) span).retag limits.retag place
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) = .ok () done
    simp only [bind,EStateM.bind]
    rw [protect]
    simp only [EStateM.bind]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) = .ok () done
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue done (sameAfter ▸ tail)
  refine ⟨reference,firstFresh,destination,secondFresh,updated,sourceChild,returnChild,sourceRaw,actualCall,?_,destOffset,
    extra,bytes,length,mutable,post,postOrder,sourceAfter,tagged,returnPositive,active⟩
  exact destId.trans (sameAllocation.symm.trans sourceId.symm)

end
end DuplicatePrefix.S02SameDestinationProtectedPacket

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationProtectedPacket.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
