import Lean
import Miri.Interpreter.ExecutionChoices
open Lean Elab Command Tactic
open Miri.Interpreter
namespace ChoiceHistory206
abbrev Tape := ExecutionChoices.Tape
abbrev Result (α : Type) := EStateM.Result StepError Tape α
private def tapeAccess : ExecutionChoices.Access Tape := ⟨id, fun _ tape => tape⟩
def compactInputs (t : Tape) : Tape :=
  { t with inputs := t.inputs.extract t.cursor t.inputs.size, cursor := 0 }
def eraseConsumedHistory (t : Tape) : Tape :=
  { compactInputs t with events := #[] }
def compactResult {α : Type} (r : Result α) : Result α :=
  match r with
  | .ok a tape => .ok a (compactInputs tape)
  | .error e tape => .error e (compactInputs tape)

private def findUnique206 (suffix : String) : CommandElabM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one imported private choice function `{suffix}`, found {candidates.length}: {candidates}"

elab "defineActualChoiceDemand206" : command => do
  let name ← findUnique206 ".Miri.Interpreter.ExecutionChoices.demand"
  let ident := mkIdent name
  let defName := mkIdent `actualChoiceDemand206
  let command ← `(command| def $defName:ident {S : Type}
    (access : ExecutionChoices.Access S) (request : ExecutionChoices.Request) :
    ExecutionChoices.M S ExecutionChoices.Input := $ident access request)
  elabCommand command

defineActualChoiceDemand206

elab "defineActualChoiceConsume206" : command => do
  let name ← findUnique206 ".Miri.Interpreter.ExecutionChoices.consume"
  let ident := mkIdent name
  let defName := mkIdent `actualChoiceConsume206
  let command ← `(command| def $defName:ident {S : Type}
    (access : ExecutionChoices.Access S) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) : ExecutionChoices.M S Unit := $ident access request input)
  elabCommand command

defineActualChoiceConsume206

private def findUniqueTactic206 (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one imported private choice function `{suffix}`, found {candidates.length}: {candidates}"

elab "simp_strict_actual_demand206" : tactic => do
  let helpers ← [
    ".Miri.Interpreter.ExecutionChoices.demand",
    ".Miri.Interpreter.ExecutionChoices.unknown"
  ].mapM findUniqueTactic206
  let helperIds := helpers.toArray.map mkIdent ++ #[
    mkIdent `ChoiceHistory206.state_get_bind_206,
    mkIdent `ChoiceHistory206.pure_apply_206,
    mkIdent `ChoiceHistory206.throw_apply_206,
    mkIdent `ChoiceHistory206.strictDemandSpec
  ]
  evalTactic (← `(tactic| unfold ChoiceHistory206.actualChoiceDemand206))
  let generated ← `(tactic| simp [tapeAccess, EStateM.run, EStateM.bind,
    EStateM.pure, EStateM.get, EStateM.instMonad, MonadState.get,
    instMonadStateOfMonadStateOf, MonadStateOf.get,
    MonadState.get, instMonadStateOfMonadStateOf, MonadStateOf.get,
    EStateM.instMonadStateOf, getThe,
    Miri.Interpreter.ExecutionChoices.Access.get,
    Miri.Interpreter.ExecutionChoices.Access.put,
    $[$helperIds:ident],*])
  evalTactic generated

inductive DemandResult where
  | ok (input : ExecutionChoices.Input) (tape : Tape)
  | error (error : StepError) (tape : Tape)
  deriving Repr

def normalizeDemandResult (r : Result ExecutionChoices.Input) : DemandResult :=
  match r with
  | .ok input tape => .ok input (eraseConsumedHistory tape)
  | .error error tape => .error error (eraseConsumedHistory tape)

theorem state_get_bind_206 {ε σ α : Type} (continuation : σ → EStateM ε σ α) (state : σ) :
    ((EStateM.get >>= continuation) state) = continuation state state := rfl

theorem pure_apply_206 {ε σ α : Type} (value : α) (state : σ) :
    ((pure value : EStateM ε σ α) state) = .ok value state := rfl

theorem throw_apply_206 {ε σ α : Type} (error : ε) (state : σ) :
    ((throw error : EStateM ε σ α) state) = .error error state := rfl

def strictDemandSpec (t : Tape) : EStateM.Result StepError Tape ExecutionChoices.Input :=
  match t.inputs[t.cursor]? with
  | some input => .ok input t
  | none => .error (.callback "choice input unknown: tape exhausted") t

theorem actual_strict_demand_spec (t : Tape) (request : ExecutionChoices.Request)
    (hpolicy : t.policy = .strict) :
    (actualChoiceDemand206 tapeAccess request).run t = strictDemandSpec t := by
  cases t with
  | mk inputs cursor policy generatedChoices diagnosticRngState events =>
    cases policy with
    | strict =>
      simp_strict_actual_demand206
      cases h : inputs[cursor]? with
      | some input => rfl
      | none => rfl
    | boundedDiagnostic maxChoices maxByteLength => simp at hpolicy
    | boundedSeededDiagnostic maxChoices maxByteLength seed => simp at hpolicy


theorem compact_idempotent (t : Tape) : compactInputs (compactInputs t) = compactInputs t := by
  cases t with
  | mk inputs cursor policy generatedChoices diagnosticRngState events =>
      simp only [compactInputs]
      congr 1
      rw [Array.extract_extract]
      simp only [Nat.add_zero, Array.size_extract, Nat.min_self]
      have hstop : min (cursor + (inputs.size - cursor)) inputs.size = inputs.size := by
        by_cases h : cursor ≤ inputs.size
        · rw [Nat.add_sub_of_le h, Nat.min_self]
        · have h' : inputs.size ≤ cursor := Nat.le_of_not_ge h
          simp [Nat.sub_eq_zero_of_le h', Nat.min_eq_right h']
      rw [hstop]

theorem compact_firstInput (t : Tape) (hcursor : t.cursor < t.inputs.size) :
    (compactInputs t).inputs[0]? = t.inputs[t.cursor]? := by
  simp only [compactInputs, Array.getElem?_extract]
  have hpositive : 0 < t.inputs.size - t.cursor := Nat.sub_pos_of_lt hcursor
  simp [hpositive, Nat.min_eq_left, Nat.add_zero]

theorem compact_firstInput_general (t : Tape) :
    (compactInputs t).inputs[0]? = t.inputs[t.cursor]? := by
  by_cases hcursor : t.cursor < t.inputs.size
  · exact compact_firstInput t hcursor
  · have hge : t.inputs.size ≤ t.cursor := Nat.le_of_not_gt hcursor
    simp [compactInputs, Array.getElem?_extract, hge]

def consumed (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) : Tape :=
  { t with cursor := t.cursor + 1, events := t.events.push ⟨request, input⟩ }

theorem actual_consume_spec (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) :
    (actualChoiceConsume206 tapeAccess request input).run t = .ok () (consumed t request input) := by
  cases t with
  | mk inputs cursor policy generatedChoices diagnosticRngState events => rfl

theorem compact_after_actual_consume (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    compactInputs (consumed t request input) =
      compactInputs (consumed (compactInputs t) request input) := by
  simp only [compactInputs, consumed, Nat.zero_add]
  congr 1
  rw [Array.extract_extract]
  simp only [Array.size_extract, Nat.min_self]
  have hstop : min (t.cursor + (t.inputs.size - t.cursor)) t.inputs.size = t.inputs.size := by
    rw [Nat.add_sub_of_le hcursor, Nat.min_self]
  rw [hstop]

theorem compactInputs_erased (t : Tape) :
    compactInputs (eraseConsumedHistory t) =
      {compactInputs (compactInputs t) with events := #[]} := by
  cases t with
  | mk inputs cursor policy generatedChoices diagnosticRngState events => rfl

theorem eraseConsumedHistory_idempotent (t : Tape) :
    eraseConsumedHistory (eraseConsumedHistory t) = eraseConsumedHistory t := by
  calc
    eraseConsumedHistory (eraseConsumedHistory t) =
        {compactInputs (eraseConsumedHistory t) with events := #[]} := rfl
    _ = {{compactInputs (compactInputs t) with events := #[]} with events := #[]} := by
        rw [compactInputs_erased]
    _ = eraseConsumedHistory t := by
        rw [compact_idempotent]
        rfl

theorem erase_history_after_actual_consume (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    eraseConsumedHistory (consumed t request input) =
      eraseConsumedHistory (consumed (eraseConsumedHistory t) request input) := by
  simp only [eraseConsumedHistory, compactInputs, consumed, Nat.zero_add]
  congr 1
  rw [Array.extract_extract]
  simp only [Array.size_extract, Nat.min_self]
  have hstop : min (t.cursor + (t.inputs.size - t.cursor)) t.inputs.size = t.inputs.size := by
    rw [Nat.add_sub_of_le hcursor, Nat.min_self]
  rw [hstop]

def eventsOfConsumeResult (result : Result Unit) : Option (Array ExecutionChoices.Event) :=
  match result with
  | .ok _ tape => some tape.events
  | .error _ _ => none

theorem actual_consume_event_appended (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) :
    eventsOfConsumeResult ((actualChoiceConsume206 tapeAccess request input).run t) =
      some (t.events.push ⟨request, input⟩) := by
  rw [actual_consume_spec]
  rfl

theorem actual_strict_demand_erased_history_independent (t : Tape)
    (request : ExecutionChoices.Request) (hpolicy : t.policy = .strict) :
    normalizeDemandResult ((actualChoiceDemand206 tapeAccess request).run t) =
      normalizeDemandResult ((actualChoiceDemand206 tapeAccess request).run (eraseConsumedHistory t)) := by
  rw [actual_strict_demand_spec t request hpolicy]
  have hpolicy' : (eraseConsumedHistory t).policy = .strict := by simpa [eraseConsumedHistory, compactInputs] using hpolicy
  rw [actual_strict_demand_spec (eraseConsumedHistory t) request hpolicy']
  have hlookup : (eraseConsumedHistory t).inputs[(eraseConsumedHistory t).cursor]? = t.inputs[t.cursor]? := by
    simpa [eraseConsumedHistory, compactInputs] using compact_firstInput_general t
  unfold normalizeDemandResult strictDemandSpec
  rw [hlookup]
  cases h : t.inputs[t.cursor]? <;> simp [h, eraseConsumedHistory_idempotent]


def normalizeConsumeResult (r : Result Unit) : Result Unit :=
  match r with
  | .ok value tape => .ok value (eraseConsumedHistory tape)
  | .error error tape => .error error (eraseConsumedHistory tape)

theorem actual_consume_erased_history_independent (t : Tape)
    (request : ExecutionChoices.Request) (input : ExecutionChoices.Input)
    (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeConsumeResult ((actualChoiceConsume206 tapeAccess request input).run t) =
      normalizeConsumeResult ((actualChoiceConsume206 tapeAccess request input).run (eraseConsumedHistory t)) := by
  rw [actual_consume_spec, actual_consume_spec]
  change EStateM.Result.ok () (eraseConsumedHistory (consumed t request input)) =
      EStateM.Result.ok () (eraseConsumedHistory (consumed (eraseConsumedHistory t) request input))
  exact congrArg (fun tape : Tape => EStateM.Result.ok () tape)
    (erase_history_after_actual_consume t request input hcursor)

#print actualChoiceDemand206
#print actualChoiceConsume206
#print axioms actual_strict_demand_erased_history_independent
#print axioms actual_consume_erased_history_independent
#print axioms actual_consume_event_appended
#print axioms actual_consume_spec
#print axioms compact_after_actual_consume

#print axioms actual_strict_demand_spec
end ChoiceHistory206
