import duplicate_prefix.S02WildcardSeparateDestinationExact

namespace DuplicatePrefix.S02WildcardSeparateDestinationTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual return tail runs after a positive wildcard argument when its
destination is a distinct concrete allocation. -/
theorem concrete_after_argument
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
      (reference.id ≠ input.contract.destination.id → ∃ final,
        (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
          (RootCallCore.argumentBody (ExecutionMachine.callHooks
            (PreparedContracts.actualConfig options () (remaining+1) span) limits)
            (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
              (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
            (EmptyRootArguments.second count))
          (Storage.withCurrent #[] root.frame machine) =
          .ok (2,2) (Storage.withCurrent #[] frame current) ∧
        RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
          (Storage.withCurrent #[] frame current) = .ok () final) := by
  obtain ⟨reference,output,firstFresh,argument,ready⟩ :=
    S02WildcardSeparateDestinationExact.concrete_after_argument_finish
      address len count input nonempty returnTag returnConcrete limits.retag
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
  let changed := {args.frame with location := FrameLocation.unwinding ⟨601⟩}
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  refine ⟨reference,output,firstFresh,?_⟩
  dsimp only
  intro different
  obtain ⟨destination,secondFresh,tree,updated,protect,_bytes,_length,_mutable,final,finish⟩ := ready different
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] args.frame
    current (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] args.frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] args.frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  refine ⟨final,argument,?_⟩
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
    RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) = .ok () final
  simp only [bind,EStateM.bind]
  rw [protect]
  simp only [EStateM.bind]
  exact finish

end
end DuplicatePrefix.S02WildcardSeparateDestinationTail

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSeparateDestinationTail.concrete_after_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard separate destination tail dependency {dependency}"
