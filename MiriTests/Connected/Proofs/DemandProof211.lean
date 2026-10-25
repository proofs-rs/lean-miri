import Lean
import Miri.Interpreter.ExecutionChoices
open Lean Elab Command Tactic
open Miri.Interpreter
namespace ChoiceDemand211
abbrev Tape := ExecutionChoices.Tape
private def tapeAccess : ExecutionChoices.Access Tape := ⟨id, fun _ tape => tape⟩

private def findUniqueDemand211 (suffix : String) : CommandElabM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one imported private choice function `{suffix}`, found {candidates.length}: {candidates}"

elab "defineActualDemand211" : command => do
  let name ← findUniqueDemand211 ".Miri.Interpreter.ExecutionChoices.demand"
  let ident := mkIdent name
  let defName := mkIdent `actualDemand211
  let command ← `(command| def $defName:ident {S : Type}
    (access : ExecutionChoices.Access S) (request : ExecutionChoices.Request) :
    ExecutionChoices.M S ExecutionChoices.Input := $ident access request)
  elabCommand command

defineActualDemand211

private def findUniqueTacticDemand211 (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one imported private choice function `{suffix}`, found {candidates.length}: {candidates}"

elab "simpStrictDemand211" : tactic => do
  let helpers ← [
    ".Miri.Interpreter.ExecutionChoices.demand",
    ".Miri.Interpreter.ExecutionChoices.unknown"
  ].mapM findUniqueTacticDemand211
  let helperIds := helpers.toArray.map mkIdent
  evalTactic (← `(tactic| unfold actualDemand211))
  evalTactic (← `(tactic| simp [tapeAccess, EStateM.run, EStateM.bind,
    EStateM.pure, EStateM.get, EStateM.throw, EStateM.instMonad,
    MonadExceptOf.throw, EStateM.instMonadExceptOfOfBacktrackable,
    MonadState.get, instMonadStateOfMonadStateOf, MonadStateOf.get,
    EStateM.instMonadStateOf, getThe,
    ExecutionChoices.Access.get, ExecutionChoices.Access.put,
    $[$helperIds:ident],*]))

theorem state_get_bind_211 {ε σ α : Type} (continuation : σ → EStateM ε σ α) (state : σ) :
    (EStateM.get >>= continuation) state = continuation state state := rfl

def strictDemandSpec (t : Tape) : EStateM.Result StepError Tape ExecutionChoices.Input :=
  match t.inputs[t.cursor]? with
  | some input => .ok input t
  | none => .error (.callback "choice input unknown: tape exhausted") t

theorem actual_strict_demand_spec (t : Tape) (request : ExecutionChoices.Request)
    (hpolicy : t.policy = .strict) :
    (actualDemand211 tapeAccess request).run t = strictDemandSpec t := by
  cases t with
  | mk inputs cursor policy generatedChoices diagnosticRngState events =>
    cases policy with
    | strict =>
      simpStrictDemand211
      simp [state_get_bind_211]
      unfold strictDemandSpec
      cases h : inputs[cursor]? with
      | some input => rfl
      | none => rfl
    | boundedDiagnostic maxChoices maxByteLength => simp at hpolicy
    | boundedSeededDiagnostic maxChoices maxByteLength seed => simp at hpolicy

#print axioms actual_strict_demand_spec
end ChoiceDemand211
