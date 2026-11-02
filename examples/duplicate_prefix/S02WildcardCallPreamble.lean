import duplicate_prefix.S02WildcardArgumentScope
import duplicate_prefix.RootEntryTail

namespace DuplicatePrefix.S02WildcardCallPreamble
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Real raw-frame push, frame lookup/update and both typed arguments for
every positive wildcard pointer in the current Contract. The destination
tail remains an explicit continuation obligation, not an assumed safety
result. -/
theorem prefix_and_continuation
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    let cfg := config options (remaining+1) span
    let h := ExecutionMachine.callHooks cfg limits
    let first := DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len
    let second := EmptyRootArguments.second count
    let raw := RawRootInvocation.root before place input.contract.model.noDataRace
    let machine := RawRootInvocation.machine #[] before
    ∃ after,
      h.withRetagMode () .FnEntry (RootCallCore.argumentBody h first second)
        (Storage.withCurrent #[] raw.frame machine) = .ok (2,2) after ∧
      ∀ done, RootEntryTail.tail h place after = .ok () done →
        Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body
          RootCompilerFacts.rootAbi #[.Copy first,.Copy second] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () done := by
  obtain ⟨reference,output,fresh,run,arguments⟩ := S02WildcardArgumentScope.argument_body
    address len count input nonempty
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let after := Storage.withCurrent #[]
    (RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
    (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker fresh
      reference.id reference.entry output.child.tree)
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits
    input.contract.model.debugOff (⟨⟨#[]⟩,before⟩ : RootState) (.memory place)
    input.contract.thread input.contract.active input.contract.emptyHarnessCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame machine
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  simp only [preamble] at unchanged
  refine ⟨after,arguments,?_⟩
  intro done tail
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push,RawRootInvocation.raw_eq #[] before place input.contract.model.noDataRace]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact tail

end
end DuplicatePrefix.S02WildcardCallPreamble

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02WildcardCallPreamble.prefix_and_continuation) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
