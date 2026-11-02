import Miri.Interpreter.ControlFlow
import Lean.Elab.Command

/-! The actual source continuation operation for an arbitrary caller stack.
These lemmas impose no execution-success premise. They isolate the final jump
of normal Return; the whole-call theorem must separately prove the preceding
production operand/pop/copy/cleanup operations and their concrete state.
-/

namespace EmptyFunction.ReturnContinuation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
variable {P L E M : Type}

/-- Restore the current caller's MIR location after a normal callee return.
Every lower frame and the entire machine payload are retained exactly. -/
def resume (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) : StepState P L E M :=
  ⟨⟨frames.push {caller with location := .mir ⟨target,0⟩}⟩,machine⟩

/-- The real continuation operation needs only a present caller. No stack
shape, heap, permissions, caller body or machine payload is fixed here. The
next step checks the target block; valid call inputs provide its existence. -/
theorem returnToBlock_push (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) :
    ControlFlow.returnToBlock (some target)
      (⟨⟨frames.push caller⟩,machine⟩ : StepState P L E M) =
      (resume frames caller machine target, .ok ()) := by
  simp [ControlFlow.returnToBlock,ControlFlow.goToBlock,ControlFlow.setLocation,
    Stack.currentFrame?, resume]

/-- A normal return to the caller cannot report any interpreter error. This
is a local theorem about the final continuation jump, not the whole Return. -/
theorem returnToBlock_no_error (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) :
    (ControlFlow.returnToBlock (some target)
      (⟨⟨frames.push caller⟩,machine⟩ : StepState P L E M)).2 = .ok () := by
  rw [returnToBlock_push]

/-- The active caller is restored with exactly the supplied next block. -/
theorem resume_current (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) :
    (resume frames caller machine target).stack.currentFrame? =
      some {caller with location := .mir ⟨target,0⟩} := by
  simp [resume, Stack.currentFrame?]

/-- The final jump preserves all previously saved frames exactly. -/
theorem resume_lower_frames (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) :
    (resume frames caller machine target).stack.frames.pop = frames := by
  simp [resume]

/-- Continuation does not execute caller code or mutate physical machine data. -/
theorem resume_machine (frames : Array (Frame P L E)) (caller : Frame P L E)
    (machine : M) (target : BasicBlockId) :
    (resume frames caller machine target).machine = machine := rfl

/-- Missing a normal-return target is an actual UB outcome, not a valid-call
case to be silently treated as success. -/
theorem missing_target (state : StepState P L E M) :
    ControlFlow.returnToBlock none state =
      (state, .error (.undefinedBehavior "Unreachable")) := rfl

end EmptyFunction.ReturnContinuation

open Lean Elab Command in
run_cmd do
  for name in #[``EmptyFunction.ReturnContinuation.returnToBlock_push,
      ``EmptyFunction.ReturnContinuation.returnToBlock_no_error,
      ``EmptyFunction.ReturnContinuation.resume_current,
      ``EmptyFunction.ReturnContinuation.resume_lower_frames,
      ``EmptyFunction.ReturnContinuation.resume_machine,
      ``EmptyFunction.ReturnContinuation.missing_target] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved empty_function continuation axiom {dependency}"
