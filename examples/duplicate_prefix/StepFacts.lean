import Miri.Interpreter.Step

/-! Driver lemmas that compose actual statement effects with the MIR program
counter update performed by the fixed interpreter. -/

namespace DuplicatePrefix.StepFacts
open Miri.MIR Miri.Interpreter

theorem step_statement {Prov Layout Extra Machine Choice Place : Type}
    (hooks : StepHooks Prov Layout Extra Machine Choice Place) (choice : Choice)
    (before after : StepState Prov Layout Extra Machine)
    (frameBefore frameAfter : Frame Prov Layout Extra)
    (locationBefore locationAfter : Location) (block : BasicBlock) (statement : Statement)
    (currentBefore : before.stack.currentFrame? = some frameBefore)
    (location : frameBefore.location = .mir locationBefore)
    (blockAt : frameBefore.body.basicBlocks[locationBefore.block]? = some block)
    (statementAt : block.statements[locationBefore.statementIndex]? = some statement)
    (effect : Step.evalStatement hooks choice statement before = (after, .ok ()))
    (sameDepth : after.stack.frames.size = before.stack.frames.size)
    (currentAfter : after.stack.currentFrame? = some frameAfter)
    (newLocation : frameAfter.location = .mir locationAfter)
    (indexValid : after.stack.frames.size - 1 < after.stack.frames.size) :
    Step.step hooks choice before =
      ({after with stack := {frames := (after.stack.frames.set (after.stack.frames.size - 1)
          {frameAfter with location := (.mir
            {locationAfter with statementIndex := locationAfter.statementIndex + 1})} indexValid)}},
        .ok true) := by
  have indexBefore : before.stack.frames.size - 1 < before.stack.frames.size := by omega
  simp [Step.step, currentBefore, location, blockAt, statementAt, effect,
    sameDepth, currentAfter, newLocation, indexBefore]

theorem step_terminator {Prov Layout Extra Machine Choice Place : Type}
    (hooks : StepHooks Prov Layout Extra Machine Choice Place) (choice : Choice)
    (before accounted after : StepState Prov Layout Extra Machine)
    (frame : Frame Prov Layout Extra) (location : Location) (block : BasicBlock)
    (current : before.stack.currentFrame? = some frame)
    (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (noStatement : block.statements[location.statementIndex]? = none)
    (accounting : hooks.beforeTerminator choice before = (accounted,.ok ()))
    (effect : hooks.terminator choice block.terminator accounted = (after,.ok ())) :
    Step.step hooks choice before = (after,.ok true) := by
  simp [Step.step, current, located, blockAt, noStatement, accounting, effect]
  rfl

end DuplicatePrefix.StepFacts
