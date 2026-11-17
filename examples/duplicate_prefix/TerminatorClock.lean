import Miri.Interpreter.TerminatorMachine

/-! Exact terminator accounting for the fixed-scheduling, GC-disabled profile.
The actual hook runs, advances counters and ticks the source virtual clock. -/
namespace DuplicatePrefix.TerminatorClock
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open Miri.ABI Miri.Memory Miri.Interpreter

def tick (clock : Clock.Monotonic Host) : Clock.Monotonic Host :=
  match clock with
  | .host epoch => .host epoch
  | .virtual n => .virtual (BitVec.ofNat 128 (n.toNat+5000))

def advance (control : TerminatorMachine.Control Host) : TerminatorMachine.Control Host :=
  {control with
    basicBlockCount := control.basicBlockCount + 1
    sinceGc := control.sinceGc + 1
    monotonic := tick control.monotonic}

open Lean Elab Tactic in
elab "unfold_terminator_control" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".TerminatorMachine.updateControl" : String) then
      some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected exact updateControl source"

theorem before_terminator [DecidableEq K]
    (hooks : TerminatorMachine.Hooks K User Host)
    (draw : MachineHooks.M K User Bool)
    (state : MachineHooks.State K User)
    (getSet : ∀ control user, hooks.getControl (hooks.setControl control user) = control)
    (setSet : ∀ first second user,
      hooks.setControl second (hooks.setControl first user) = hooks.setControl second user)
    (unchecked : (hooks.getControl state.machine.user).checkedArithmetic = false)
    (noGc : (hooks.getControl state.machine.user).gcInterval = 0)
    (fixed : state.machine.threads.fixedScheduling = true) :
    TerminatorMachine.beforeTerminatorWithChoice hooks draw state =
      .ok () {state with machine := {state.machine with user :=
        (hooks.setControl (advance (hooks.getControl state.machine.user)) state.machine.user)}} := by
  unfold TerminatorMachine.beforeTerminatorWithChoice
  unfold_terminator_control
  cases clock : (hooks.getControl state.machine.user).monotonic <;>
    simp_all (config := {maxSteps := 1000000}) [TerminatorMachine.maybePreemptWithChoice, Clock.Monotonic.tick,
      advance, tick, get, getThe, MonadStateOf.get, EStateM.get,
      set, MonadStateOf.set, EStateM.set, bind, EStateM.bind, pure, EStateM.pure,
      Except.bind, Except.pure]

#print axioms before_terminator
end DuplicatePrefix.TerminatorClock
