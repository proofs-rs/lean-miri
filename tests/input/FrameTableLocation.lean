import Miri.Interpreter.Step

open Miri Miri.MIR Miri.Interpreter

private def missingBlock (frame : Frame Unit Unit Unit) : Frame Unit Unit Unit :=
  {frame with
    body := {frame.body with basicBlocks := #[⟨7⟩]}
    mirTables := {frame.mirTables with blocks := #[]}
    location := .mir ⟨0,0⟩}

example (frame : Frame Unit Unit Unit) :
    (missingBlock frame).setLocation (.mir ⟨0,0⟩) = .error (.invalidLocation ⟨0,0⟩) := by
  simp [missingBlock, Frame.setLocation, MIR.SharedTable.lookup,
    throw, throwThe, MonadExceptOf.throw]

example (frame : Frame Unit Unit Unit) :
    (missingBlock frame).instruction? = .error (.invalidMirReference "block" 7) := by
  apply Frame.instruction_missing_block _ ⟨0,0⟩ ⟨7⟩ rfl rfl
  rfl

example (frame : Frame Unit Unit Unit) (hooks : StepHooks Unit Unit Unit Unit Unit Unit) :
    let state : StepState Unit Unit Unit Unit := ⟨⟨#[missingBlock frame]⟩,()⟩
    Step.step hooks () state = (state,.error (.invalidProgram "invalid MIR block ID 7")) := by
  simp [Step.step, missingBlock, Stack.currentFrame?, MIR.SharedTable.lookup]
  rfl
