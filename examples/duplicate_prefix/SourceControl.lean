import duplicate_prefix.Storage
import duplicate_prefix.StepFacts
import duplicate_prefix.TerminatorClock
import Miri.Interpreter.ExecutionMachine

namespace DuplicatePrefix.SourceControl
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def accounted (hooks : TerminatorMachine.Hooks K User Host)
    (state : MachineHooks.State K User) : MachineHooks.State K User :=
  {state with machine := {state.machine with user :=
    (hooks.setControl (TerminatorClock.advance (hooks.getControl state.machine.user)) state.machine.user)}}

theorem before_terminator [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (state : MachineHooks.State K User)
    (getSet : ∀ control user,
      config.terminators.getControl (config.terminators.setControl control user) = control)
    (setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) =
        config.terminators.setControl second user)
    (unchecked : (config.terminators.getControl state.machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl state.machine.user).gcInterval = 0)
    (fixed : state.machine.threads.fixedScheduling = true) :
    (ExecutionMachine.stepHooks config limits).beforeTerminator choice state =
      (accounted config.terminators state,.ok ()) := by
  change MachineHooks.run
    (TerminatorMachine.beforeTerminatorWithChoice config.terminators (config.preemptionChoice choice)) state = _
  unfold MachineHooks.run Call.run
  rw [TerminatorClock.before_terminator config.terminators _ state getSet setSet unchecked noGc fixed]
  rfl

theorem goto_step [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User)
    (location : Location) (block : BasicBlock) (target : BasicBlockId)
    (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (noStatement : block.statements[location.statementIndex]? = none)
    (gotoKind : ∃ source, block.terminator.kind = .Goto target source)
    (getSet : ∀ control user,
      config.terminators.getControl (config.terminators.setControl control user) = control)
    (setSet : ∀ first second user,
      config.terminators.setControl second (config.terminators.setControl first user) =
        config.terminators.setControl second user)
    (unchecked : (config.terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : (config.terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    ExecutionMachine.step config limits choice (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore {frame with location := .mir ⟨target,0⟩}
        (accounted config.terminators (Storage.withCurrent framesBefore frame machine)).machine,
        .ok true) := by
  let before := Storage.withCurrent framesBefore frame machine
  let next := accounted config.terminators before
  have accounting := before_terminator config limits choice before getSet setSet unchecked noGc fixed
  have effect : (ExecutionMachine.stepHooks config limits).terminator choice block.terminator next =
      (Storage.withCurrent framesBefore {frame with location := .mir ⟨target,0⟩} next.machine,.ok ()) := by
    change ControlFlow.evalTerminator _ choice block.terminator next = _
    obtain ⟨source, kind⟩ := gotoKind
    unfold ControlFlow.evalTerminator
    rw [kind]
    simp [ControlFlow.goToBlock, ControlFlow.setLocation, next, accounted, before,
      Storage.withCurrent, Stack.currentFrame?]
  exact StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) choice before next _
    frame location block (by simp [before, Storage.withCurrent, Stack.currentFrame?])
    located blockAt noStatement accounting effect

theorem switch_one {P Layout Extra Machine Choice Op Imm : Type}
    (hooks : TerminatorHooks P Layout Extra Machine Choice Op Imm) (choice : Choice)
    (terminator : Terminator) (discriminant : Miri.MIR.Operand)
    (bits : Nat) (matched otherwise : BasicBlockId)
    (before evaluated compared : StepState P Layout Extra Machine)
    (value : Imm) (equal : Bool)
    (kind : terminator.kind = .SwitchInt discriminant ⟨#[.Case bits matched],otherwise⟩)
    (evaluation : hooks.evalDiscriminant choice discriminant before = (evaluated,.ok value))
    (comparison : hooks.compareSwitchCase choice value bits evaluated = (compared,.ok equal)) :
    ControlFlow.evalTerminator hooks choice terminator before =
      ControlFlow.goToBlock (if equal then matched else otherwise) compared := by
  unfold ControlFlow.evalTerminator
  rw [kind]
  simp only [evaluation]
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
  cases equal <;> simp [comparison]

#print axioms switch_one

#print axioms goto_step
end DuplicatePrefix.SourceControl
