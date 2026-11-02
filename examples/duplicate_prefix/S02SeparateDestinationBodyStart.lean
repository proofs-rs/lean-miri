import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.S02SeparateDestinationSourceReady
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame

namespace DuplicatePrefix.S02SeparateDestinationBodyStart
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual call-entry result retains the source's full Positive window
authorization in the distinct-concrete return case. The return protector,
uninit write, finish, and call prefix all execute on one witness/state. -/
theorem concrete_positive_body_start
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
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (sourceTracker : MachineHooks.BorrowState) (child : UniIndex) (done : RootState),
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first := DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len
      let second := EmptyRootArguments.second count
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body
        RootCompilerFacts.rootAbi #[.Copy first,.Copy second] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () done ∧
      done.machine.borrowTracker = some sourceTracker ∧
      done.machine.memory.live.find? (fun row => row.1 == reference.id) =
        some (reference.id,sourceEntry) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        sourceTracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len) := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,tree,updated,protect,_bytes,_length,_mutable,
      _unusedFinal,_unusedFinish⟩ :=
    S02SeparateDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      different returnTag returnConcrete limits.retag
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
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let done := Storage.withCurrent #[]
    (CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}) after.machine
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra finalTree}
  obtain ⟨child,raw,same,_parent,_offset,_length,sourceLive,enabled,runtime,⟨positive⟩⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have trackerEq : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
        reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans enabled)
  have globalEq : destination.tracker.global =
      TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh :=
    congrArg MachineHooks.BorrowState.global trackerEq
  rw [←globalEq] at runtime positive
  have separate : destination.id ≠ reference.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have pointer := congrArg (fun p : Pointer (Option Provenance) => p.provenance) physical
    simp only [Pointer.withOptionalProvenance] at pointer
    have concrete : destination.pointer.provenance =
        .concrete input.contract.destination.id returnTag :=
      (Option.some.inj pointer).trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    have destId : destination.id = input.contract.destination.id := binding.1.symm
    simpa only [destId,same] using Ne.symm different
  obtain ⟨sourceTracker,trackerAfter,liveAfter,⟨positiveAfter⟩⟩ :=
    S02SeparateDestinationSourceReady.source_positive_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id sourceEntry separate sourceLive runtime
      (some child) (some raw.selected) raw.maximum reference.offset len positive
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
  refine ⟨reference,raw,sourceEntry,sourceTracker,child,done,actualCall,?_ ,?_,⟨positiveAfter⟩⟩
  · exact trackerAfter
  · exact liveAfter

end
end DuplicatePrefix.S02SeparateDestinationBodyStart

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationBodyStart.concrete_positive_body_start) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination body-start dependency {dependency}"
