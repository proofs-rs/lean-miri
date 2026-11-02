import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.S02ConcreteCallPreamble

namespace DuplicatePrefix.S02SeparateDestinationMachineSettings
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact second protection and uninit store preserve the machine control
settings needed by the nonzero-count body prefix. All settings originate in
the call-time model; the actual protection is a conclusion. -/
theorem after_exact
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
      (tracker : MachineHooks.BorrowState)
      (installed : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post) ∧
      post.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
      post.user.payload.ghost = false ∧ post.user.payload.validation = .Shallow ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl post.user).gcInterval = 0 ∧
      post.threads.fixedScheduling = true ∧ post.dataRace = none := by
  obtain ⟨reference,firstFresh,_argument,destination,secondFresh,tree,updated,_protect,_bytes,_length,_mutable,
      _unusedFinal,_unusedFinish⟩ :=
    S02SeparateDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      different returnTag returnConcrete limits.retag
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
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
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
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
    rw [_protect]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) =
        .ok () (Storage.withCurrent #[] installed after.machine)
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans _argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue (Storage.withCurrent #[] installed after.machine) (sameAfter ▸ tail)
  let next := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have tracked : after.machine.borrowTracker = some next := rfl
  obtain ⟨originalTracker,originalEnabled,originalMode⟩ := input.contract.model.defaultTracker
  have refMode : reference.tracker.retagMode = .Default := by
    have same : reference.tracker = originalTracker :=
      Option.some.inj (reference.enabled.symm.trans originalEnabled)
    rw [same]
    exact originalMode
  have destMode : destination.tracker.retagMode = .Default := by
    have same : destination.tracker =
        ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh, reference.tracker.retagMode⟩ := by
      exact Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh, reference.tracker.retagMode⟩ from rfl))
    rw [same]
    exact refMode
  have nextMode : next.retagMode = .Default := by
    simpa only [next,TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker] using destMode
  obtain ⟨_,_,raceEq,_,ghostEq,shallowEq,_,_,_⟩ := RawRootInvocation.preservation #[] before
  have postUser : after.machine.user = machine.user := rfl
  have postThreads : after.machine.threads = machine.threads := rfl
  have postRace : after.machine.dataRace = machine.dataRace := rfl
  refine ⟨reference,next,installed,after.machine,actualCall,tracked,nextMode,?_,?_,?_,?_,?_,?_⟩
  · rw [postUser,ghostEq]
    exact input.contract.model.ghostOff
  · rw [postUser,shallowEq]
    exact input.contract.model.shallow
  · rw [postUser]
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact input.contract.model.unchecked
  · rw [postUser]
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact input.contract.model.noGc
  · rw [postThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  · rw [postRace,raceEq]
    exact input.contract.model.noDataRace

end
end DuplicatePrefix.S02SeparateDestinationMachineSettings

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationMachineSettings.after_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate machine settings dependency {dependency}"
