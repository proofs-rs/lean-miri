import duplicate_prefix.S02WildcardSourceWildcardReturnPacketArgument
import duplicate_prefix.S02WildcardCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02WildcardSourceWildcardInstalledIdentity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual installed stack frame has the wildcard return packet produced
by the same real argument and protector operations. -/
theorem enters_identity
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len)
      (output : GeneralBorrowForestFnEntry.Output)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      reference.id ≠ input.contract.destination.id →
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input
        (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
          (RawRootInvocation.machine #[] before) reference.tracker firstFresh
          reference.id reference.entry output.child.tree) place)
      (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
      (tree : BorrowTree) (updated : Allocation Provenance BorrowTree),
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
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
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
      let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
        destination.tracker.global.nextPointerTag
      let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed after.machine) ∧
      destination.id = input.contract.destination.id ∧
      ∃ packet : S02ConcreteSourceWildcardReturnPacket.ReturnPacket after.machine place reference.id
        reference.tracker.global.nextPointerTag borrowFrame, packet.destination.id = destination.id := by
  obtain ⟨reference,output,firstFresh,ready⟩ :=
    S02WildcardSourceWildcardReturnPacketArgument.after_protection
      address len count input nonempty returnWildcard
  refine ⟨reference,output,firstFresh,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,_run,argument,destId,_destEntry,protect,packet,packetId⟩ :=
    ready different
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
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let done := Storage.withCurrent #[] installed after.machine
  obtain ⟨body,size,dead,noClocks⟩ := S02PositiveFinishFrame.after_destination_registration root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count
    reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame
    after.machine body size
    (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
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
  obtain ⟨preamble,preambleArg,preambleContinue⟩ :=
    S02WildcardCallPreamble.prefix_and_continuation address len count input nonempty
  have sameAfter : preamble = Storage.withCurrent #[] frame current := by
    exact (EStateM.Result.ok.inj (preambleArg.symm.trans argument)).2
  exact ⟨destination,secondFresh,tree,updated,
    preambleContinue done (sameAfter ▸ tail),destId,packet,packetId⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardInstalledIdentity

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardInstalledIdentity.enters_identity) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard installed dependency {dependency}"
