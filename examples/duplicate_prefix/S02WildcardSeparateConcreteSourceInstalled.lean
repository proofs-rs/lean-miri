import duplicate_prefix.S02WildcardSeparateConcreteProtectSource
import duplicate_prefix.S02WildcardCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02WildcardSeparateConcreteSourceInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual root call is fully initialized, retaining source rights in
the installed machine after wildcard FnEntry and concrete return protection. -/
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
        (Pointer.new .wildcard (Size.ofBytes address)) len),
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
          sourceEntry.allocation.extra.nodes.size < 65536 := by
  obtain ⟨reference,output,firstFresh,argument,ready⟩ :=
    S02WildcardSeparateConcreteProtectSource.source_after_protect address len count input nonempty
      returnTag returnConcrete
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count
  let changed := {args.frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree}
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,sourceChild,sourceNode,sourceTracker,
    protect,tracked,sourceLive,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort⟩ := ready different
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
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
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] args.frame
    current (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] args.frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] args.frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] args.frame current) =
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
    simp only [EStateM.bind, Bool.not_true, ite_false, pure, EStateM.pure]
    change (do
      TypedRetag.protectInPlaceFunctionArgument
        (config options (remaining+1) span).retag limits.retag place
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) =
        .ok () (Storage.withCurrent #[] installed after.machine)
    simp only [bind,EStateM.bind]
    rw [protect]
    simp only [EStateM.bind]
    exact finish
  obtain ⟨prefixState,preambleArg,preambleContinue⟩ :=
    S02WildcardCallPreamble.prefix_and_continuation address len count input nonempty
  have sameAfter : prefixState = Storage.withCurrent #[] args.frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actual := preambleContinue _ (sameAfter ▸ tail)
  exact ⟨installed,after.machine,sourceEntry,sourceChild,sourceNode,sourceTracker,
    actual,tracked,sourceLive,sourceTagged,sourcePresent,sourceTag,parentless,leaf,hidden,
    sourceRuntime,sourcePositive,sourceActivity,sourceDistinct,sourceOrder,sourceShort⟩

end
end DuplicatePrefix.S02WildcardSeparateConcreteSourceInstalled

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms
      ``DuplicatePrefix.S02WildcardSeparateConcreteSourceInstalled.installed) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate concrete source-installed dependency {dependency}"
