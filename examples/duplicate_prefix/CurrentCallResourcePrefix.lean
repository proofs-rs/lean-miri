import duplicate_prefix.CurrentCallResourceEntryFacts
namespace DuplicatePrefix.CurrentCallResourcePrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : CurrentCallResourceEntryBody.Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : CurrentCallResourceEntryBody.Output limits C count)


theorem before_shared (nonzero : count≠0) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span out.finalMachine)) ∧
      GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) result count :=
  (CurrentCallBodyPrefix.body_prefix_of_installed options limits remaining span root C.rawLocals
  (CurrentCallTypedSourceCopy.value options remaining span
    (CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag) len).imm
  count C.borrowFrame id tracker.global.nextPointerTag out.physical.id out.sourceOutput.global.nextPointerTag
  (CurrentCallResourceEntry.finishedFrame out) out.finalMachine (CurrentCallResourceEntryFacts.installed_eq out)
  (CurrentCallResourceEntryFacts.model out) C.validationFuel C.validationEq).2 nonzero

theorem before_zero_return (zero : count=0) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span out.finalMachine))) ∧
      result.body=RootBody.reflected.body.body ∧ result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧ result.locals.size=25 ∧ result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=(CurrentCallResourceEntry.finishedFrame out).returnPlace ∧
      result.extra=(CurrentCallResourceEntry.finishedFrame out).extra ∧
      result.returnContinuation=(CurrentCallResourceEntry.finishedFrame out).returnContinuation ∧
      result.vaList=(CurrentCallResourceEntry.finishedFrame out).vaList ∧ CopyHelperCleanup.AllImmediate result :=
  (CurrentCallBodyPrefix.body_prefix_of_installed options limits remaining span root C.rawLocals
  (CurrentCallTypedSourceCopy.value options remaining span
    (CurrentCallTypedFnEntry.changedPointer W.pointer.value id tracker.global.nextPointerTag) len).imm
  count C.borrowFrame id tracker.global.nextPointerTag out.physical.id out.sourceOutput.global.nextPointerTag
  (CurrentCallResourceEntry.finishedFrame out) out.finalMachine (CurrentCallResourceEntryFacts.installed_eq out)
  (CurrentCallResourceEntryFacts.model out) C.validationFuel C.validationEq).1 zero

end
end DuplicatePrefix.CurrentCallResourcePrefix
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourcePrefix" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource-prefix dependency {dependency}"
