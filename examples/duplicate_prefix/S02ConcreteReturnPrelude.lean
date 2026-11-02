import duplicate_prefix.S02ConcreteArgumentScope
import duplicate_prefix.RootEntryTail

namespace DuplicatePrefix.S02ConcreteReturnPrelude
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact first two operations of `RootEntryTail.tail`, stopping just
before the actual destination protector. -/
def before_protect (h : RootCallCore.RootHooks) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  RootCallCore.spanAt h (← h.localSpan RootBody.reflected.body.body 0)
  unless ← h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")

/-- After the actual positive concrete argument passes, the return span and
ABI check succeed on their derived frame and machine. No destination borrow
operation, return-slot shape, or tail success is assumed. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (fresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let machine := RawRootInvocation.machine #[] before
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let args := RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) count
      let afterMachine := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
        reference.id reference.entry tag reference.offset len
      before_protect (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        (Storage.withCurrent #[] args.frame afterMachine) =
        .ok () (Storage.withCurrent #[] {args.frame with location := .unwinding ⟨601⟩} afterMachine) := by
  obtain ⟨reference,fresh,_arguments⟩ := S02ConcreteArgumentScope.argument_body
    id tag address len count input nonempty
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let machine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count
  let afterMachine := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker fresh
    reference.id reference.entry tag reference.offset len
  let changed := {args.frame with location := FrameLocation.unwinding ⟨601⟩}
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] args.frame
    afterMachine args.body args.identity args.callee
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] args.frame afterMachine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] args.frame changed afterMachine
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed afterMachine) = .ok true (Storage.withCurrent #[] changed afterMachine) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  refine ⟨reference,fresh,?_⟩
  unfold before_protect RootCallCore.spanAt
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
  simp only [ite_true,pure,EStateM.pure]
  rfl

end
end DuplicatePrefix.S02ConcreteReturnPrelude
