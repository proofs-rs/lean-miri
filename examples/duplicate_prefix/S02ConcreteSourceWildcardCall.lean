import duplicate_prefix.S02ConcreteSourceWildcardExact
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.RootEntryTail

namespace DuplicatePrefix.S02ConcreteSourceWildcardCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive concrete call initializes its root frame with a
distinct wildcard return allocation. No later body execution is assumed. -/
theorem actual_entry
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ final, Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
        .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () final := by
  obtain ⟨reference,fresh,argument,destination,secondFresh,tree,updated,protect,_,_,_,
    final,finish⟩ := S02ConcreteSourceWildcardExact.after_argument_exact id tag address len count
      input nonempty different returnWildcard limits.retag
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count
  let changed := {args.frame with location := FrameLocation.unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] args.frame
    current (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] args.frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] args.frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] args.frame current) = .ok () final := by
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
  obtain ⟨preamble,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preamble = Storage.withCurrent #[] args.frame current := by
    exact (EStateM.Result.ok.inj (preambleArg.symm.trans argument)).2
  exact ⟨final,preambleContinue final (sameAfter ▸ tail)⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardCall

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardCall.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard call dependency {dependency}"
