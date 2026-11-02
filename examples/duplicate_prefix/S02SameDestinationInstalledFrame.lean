import duplicate_prefix.S02SameDestinationInit
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.AsMutPushPreserves

namespace DuplicatePrefix.S02SameDestinationInstalledFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Shape of the actual positive call's installed root frame. In particular,
the length-call frontend receives a concrete source and the original count. -/
theorem concrete_positive_installed
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (destinationId : AllocId) (destinationTag : BorTag)
      (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      frame = PositiveRootInstalledFrame.installed
        (RawRootInvocation.root before place input.contract.model.noDataRace)
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
        count {} reference.id reference.tracker.global.nextPointerTag destinationId destinationTag ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.bodyIdentity = RootBody.reflected.body.identity ∧
      frame.functionInstance = RootBody.reflected.functionInstance ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.locals.size = 25 ∧
      frame.locals[1]? = some ⟨.live (.immediate
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
        some ActualReferenceMetadata.reference⟩ ∧
      frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),
        some RootCompilerFacts.usizeLayout⟩ ∧
      machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime ∧
      machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false ∧
      ∃ thread, machine.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0 := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,tree,updated,protect,_bytes,_length,_mutable,
      _unusedFinal,_unusedFinish⟩ :=
    S02SameDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      sameAllocation returnTag returnConcrete limits.retag
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := PositiveRootInstalledFrame.installed raw adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have installedEq : installed = CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩} := rfl
  have shape := PositiveRootInstalledFrame.metadata raw adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have size := PositiveRootInstalledFrame.size raw adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have slot1 := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
    ⟨1,by decide⟩
  have slot2 := PositiveRootInstalledFrame.slot_option raw
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
    ⟨2,by decide⟩
  have finishShape := S02PositiveFinishFrame.after_destination_registration raw
    (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  obtain ⟨body,frameSize,dead,noClocks⟩ := finishShape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine
    body frameSize (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
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
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] frame current) =
      .ok () (Storage.withCurrent #[] installed after.machine) := by
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
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) =
        .ok () (Storage.withCurrent #[] installed after.machine)
    simp only [bind,EStateM.bind]
    rw [protect]
    simp only [EStateM.bind]
    rw [installedEq]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) =
        .ok () (Storage.withCurrent #[]
          (CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}) after.machine)
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue (Storage.withCurrent #[] installed after.machine) (sameAfter ▸ tail)
  obtain ⟨_,_,_,_,_,_,typesEq,_,_⟩ := RawRootInvocation.preservation #[] before
  have currentTypes : after.machine.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.types = _
    exact typesEq
  have rootActive : machine.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have afterActive : after.machine.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change machine.threads.activeThread? = _
    exact rootActive
  refine ⟨reference,destination.id,destination.tracker.global.nextPointerTag,installed,after.machine,actualCall,rfl,shape.1.trans raw.body,
    shape.2.1.trans raw.identity,shape.2.2.1.trans raw.callee,shape.2.2.2.2.2.2.2.2,size,?_,?_,?_,?_,?_⟩
  · simpa [installed,adjusted] using slot1
  · simpa [installed] using slot2
  · rw [currentTypes]
    exact input.contract.model.metadata
  · rw [currentTypes]
    exact input.slice_not_constructed
  · exact ⟨{input.contract.thread with topUserRelevantFrame := some 0},afterActive,rfl⟩

end
end DuplicatePrefix.S02SameDestinationInstalledFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationInstalledFrame.concrete_positive_installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete installed-frame dependency {dependency}"
