import duplicate_prefix.CurrentCallResourcePreparedEntry

namespace DuplicatePrefix.CurrentCallResourceEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def root (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) : RootFrame :=
  RootFrameData.raw (CurrentCallPush.preparedMachine before frames) (.memory place)
    (CallEntryFacts.freshRoot before).2 race

def finishedFrame {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : CurrentCallResourceEntryBody.Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : CurrentCallResourceEntryBody.Output limits C count) : CompilerFrameContext.ActualFrame :=
  CallEntryFacts.doneRootFrame {registeredFrame (atSpan out.argsRoot ⟨601⟩).frame out.sourceOutput.frame out.physical.id
    out.sourceOutput.global.nextPointerTag with location:=.unwinding ⟨559⟩}

/-- Actual full root initialization from normalized current resources. The
initial state is unchanged: raw push precedes both argument copies, destination
protection, and frame finish. Ordinary admission is not asserted here. -/
theorem invoke {options remaining span frames before tracker data owner id offset len W place}
    (limits : ExecutionMachine.Limits) (race : before.dataRace=none)
    (C : CurrentCallResourceEntryBody.Conditions options remaining span frames (root before frames place race)
      before tracker data owner id offset len W place)
    (stackReady : CurrentCallPush.StackReadiness before frames) (count : UInt64) :
    ∃ out : CurrentCallResourceEntryBody.Output limits (CurrentCallResourcePreparedEntry.prepared C) count,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩,
          .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (finishedFrame out) out.finalMachine) := by
  obtain ⟨out⟩ := CurrentCallResourceEntryBody.invoke limits (CurrentCallResourcePreparedEntry.prepared C) count
  let initialRoot := root before frames place race
  let machine := CurrentCallPush.preparedMachine before frames
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have push := CurrentCallPush.push options (remaining+1) span limits C.model.debugOff before frames (.memory place) stackReady
  have rawEq : CallEntryFacts.rawPushedState frames before (.memory place)=Storage.withCurrent frames initialRoot.frame machine := rfl
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames initialRoot.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames initialRoot.frame initialRoot.frame machine
  have preamble : initialRoot.frame.location=.unwinding ⟨559⟩ := rfl
  have trackNone : initialRoot.frame.trackCallerArg=none := rfl
  have unchanged : {initialRoot.frame with trackCallerArg:=none}=initialRoot.frame := by rw [←trackNone]
  have arguments : h.withRetagMode () .FnEntry (RootCallCore.argumentBody h
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span W.pointer.value len).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames initialRoot.frame machine)=.ok (2,2) (Storage.withCurrent frames out.argsRoot.frame out.sourceMachine) := out.arguments
  refine ⟨out,?_⟩
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  rw [push,rawEq]
  dsimp only
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged,setFrame]
  dsimp only
  erw [arguments]
  dsimp only
  exact out.tail

end
end DuplicatePrefix.CurrentCallResourceEntry
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceEntry" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generic resource entry dependency {dependency}"
