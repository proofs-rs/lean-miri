import duplicate_prefix.S02SeparateDestinationTail
import duplicate_prefix.S02ConcreteCallPreamble

namespace DuplicatePrefix.S02SeparateDestinationInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real root call entry, through positive argument retag, separate
concrete return protection, and root entry finish. -/
theorem concrete_positive_call
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
    ∃ done,
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first := DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len
      let second := EmptyRootArguments.second count
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body
        RootCompilerFacts.rootAbi #[.Copy first,.Copy second] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () done := by
  obtain ⟨reference,fresh,done,arguments,tail⟩ :=
    S02SeparateDestinationTail.concrete_after_argument id tag address len count input nonempty
      different returnTag returnConcrete
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let after := Storage.withCurrent #[]
    (RootArgumentsTwo.result (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
    (GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
      reference.id reference.entry tag reference.offset len)
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits
    input.contract.model.debugOff (⟨⟨#[]⟩,before⟩ : RootState) (.memory place)
    input.contract.thread input.contract.active input.contract.emptyHarnessCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame machine
  have control := RawRootInvocation.control before place input.contract.model.noDataRace
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  simp only [preamble] at unchanged
  refine ⟨done,?_⟩
  dsimp only
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
end DuplicatePrefix.S02SeparateDestinationInit

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationInit.concrete_positive_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination init dependency {dependency}"
