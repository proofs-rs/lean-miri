import Lean
import Miri.Interpreter.ExecutionChoices
open Lean Elab Command Tactic
open Miri.Interpreter
namespace ChoiceLocality220
/- The private demand/consume source mapping and history lemmas below are a
verifier-local reuse of choice-history206/attempt-049/ChoiceHistory206.lean
(SHA-256 794b3a59ae03856b2962ca6f32b1f523cc6ea48e5636e95ed2cab2b1e403780b).
The five public wrapper theorems below call the imported source definitions
directly. -/
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

elab "defineActualChoiceUnknown220" : command => do
  let name ← findUnique206 ".Miri.Interpreter.ExecutionChoices.unknown"
  let ident := mkIdent name
  let defName := mkIdent `actualChoiceUnknown220
  let command ← `(command| def $defName:ident {S A : Type}
    (message : String) : ExecutionChoices.M S A := $ident message)
  elabCommand command

defineActualChoiceUnknown220

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
    mkIdent `ChoiceLocality220.state_get_bind_206,
    mkIdent `ChoiceLocality220.pure_apply_206,
    mkIdent `ChoiceLocality220.throw_apply_206,
    mkIdent `ChoiceLocality220.strictDemandSpec
  ]
  evalTactic (← `(tactic| unfold ChoiceLocality220.actualChoiceDemand206))
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


def normalizeChoiceResult {α : Type} (r : Result α) : EStateM.Result StepError Tape α :=
  match r with
  | .ok value tape => .ok value (eraseConsumedHistory tape)
  | .error error tape => .error error (eraseConsumedHistory tape)

theorem erase_firstInput_general (t : Tape) :
    (eraseConsumedHistory t).inputs[(eraseConsumedHistory t).cursor]? = t.inputs[t.cursor]? := by
  simpa [eraseConsumedHistory, compactInputs] using compact_firstInput_general t

elab "simp_public_choice220" : tactic => do
  let helpers ← [
    ".Miri.Interpreter.ExecutionChoices.demand",
    ".Miri.Interpreter.ExecutionChoices.consume",
    ".Miri.Interpreter.ExecutionChoices.unknown"
  ].mapM findUniqueTactic206
  let helperIds := helpers.toArray.map mkIdent ++ #[
    mkIdent `ChoiceLocality220.actual_strict_demand_spec,
    mkIdent `ChoiceLocality220.actual_consume_spec,
    mkIdent `ChoiceLocality220.state_get_bind_206,
    mkIdent `ChoiceLocality220.pure_apply_206,
    mkIdent `ChoiceLocality220.throw_apply_206,
    mkIdent `ChoiceLocality220.erase_history_after_actual_consume,
    mkIdent `ChoiceLocality220.eraseConsumedHistory_idempotent,
    mkIdent `ChoiceLocality220.compact_firstInput_general,
    mkIdent `ChoiceLocality220.erase_firstInput_general
  ]
  let generated ← `(tactic| simp [
    ChoiceLocality220.tapeAccess,
    ChoiceLocality220.normalizeChoiceResult,
    ChoiceLocality220.eraseConsumedHistory,
    ChoiceLocality220.compactInputs,
    Miri.Interpreter.ExecutionChoices.index,
    Miri.Interpreter.ExecutionChoices.boolean,
    Miri.Interpreter.ExecutionChoices.bernoulli,
    Miri.Interpreter.ExecutionChoices.integer,
    Miri.Interpreter.ExecutionChoices.bytes,
    EStateM.run, EStateM.bind, EStateM.pure,
    EStateM.get, EStateM.instMonad, MonadState.get,
    instMonadStateOfMonadStateOf, MonadStateOf.get,
    EStateM.instMonadStateOf, getThe,
    Miri.Interpreter.ExecutionChoices.Access.get,
    Miri.Interpreter.ExecutionChoices.Access.put,
    $[$helperIds:ident],*])
  evalTactic generated

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


theorem strict_demand_bind_spec220 {α : Type}
    (t : Tape) (request : ExecutionChoices.Request)
    (continuation : ExecutionChoices.Input → ExecutionChoices.M Tape α)
    (hpolicy : t.policy = .strict) :
    ((actualChoiceDemand206 tapeAccess request >>= continuation).run t) =
      match strictDemandSpec t with
      | .ok input state => (continuation input).run state
      | .error error state => .error error state := by
  change (EStateM.bind (actualChoiceDemand206 tapeAccess request) continuation) t = _
  simp only [EStateM.bind]
  have hd := actual_strict_demand_spec t request hpolicy
  change actualChoiceDemand206 tapeAccess request t = strictDemandSpec t at hd
  rw [hd]
  cases hs : strictDemandSpec t <;> simp [hs, strictDemandSpec, EStateM.run]

def sourceIndexContinuation220 (site : ExecutionChoices.IndexSite) (count : Nat)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Nat := do
  let .index actual value := input | actualChoiceUnknown220 s!"expected index at {repr site}"
  unless actual == site do actualChoiceUnknown220 s!"index site mismatch at {repr site}"
  unless value < count do actualChoiceUnknown220 s!"index outside support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.index site count) input
  pure value

def sourceIndex220 (site : ExecutionChoices.IndexSite) (count : Nat) :
    ExecutionChoices.M Tape Nat := do
  if count == 0 then
    throw (.invalidProgram "source random selection has empty support")
  let request := ExecutionChoices.Request.index site count
  let input ← actualChoiceDemand206 tapeAccess request
  sourceIndexContinuation220 site count input

theorem public_index_eq_source_spec220 (site : ExecutionChoices.IndexSite) (count : Nat) :
    ExecutionChoices.index tapeAccess site count = sourceIndex220 site count := rfl

elab "simp_actual_unknown220" : tactic => do
  let name ← findUniqueTactic206 ".Miri.Interpreter.ExecutionChoices.unknown"
  let id := mkIdent name
  evalTactic (← `(tactic| simp [$id:ident, EStateM.run]))

theorem actualChoiceUnknown_spec220 {S A : Type} (message : String) (state : S) :
    (@actualChoiceUnknown220 S A message).run state =
      (EStateM.Result.error (.callback s!"choice input unknown: {message}") state : EStateM.Result StepError S A) := by
  unfold actualChoiceUnknown220
  change (throw (StepError.callback s!"choice input unknown: {message}") : EStateM StepError S A) state = _
  exact throw_apply_206 (StepError.callback s!"choice input unknown: {message}") state

theorem actualChoiceConsume_map_spec220 (t : Tape) (request : ExecutionChoices.Request)
    (input : ExecutionChoices.Input) {α : Type} (value : α) :
    ((fun _ : Unit => value) <$> actualChoiceConsume206 tapeAccess request input).run t =
      .ok value (consumed t request input) := by
  change EStateM.map (fun _ : Unit => value)
    (actualChoiceConsume206 tapeAccess request input) t = _
  unfold EStateM.map
  have hc := actual_consume_spec t request input
  change actualChoiceConsume206 tapeAccess request input t =
    EStateM.Result.ok () (consumed t request input) at hc
  rw [hc]

theorem sourceIndexContinuation_erased220 (t : Tape) (site : ExecutionChoices.IndexSite)
    (count : Nat) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceIndexContinuation220 site count input).run t) =
      normalizeChoiceResult ((sourceIndexContinuation220 site count input).run (eraseConsumedHistory t)) := by
  cases input with
  | index actual value =>
      by_cases hsite : actual = site
      · by_cases hvalue : value < count
        · simp [sourceIndexContinuation220, hsite, hvalue,
            actualChoiceConsume_map_spec220, normalizeChoiceResult]
          exact erase_history_after_actual_consume t (ExecutionChoices.Request.index site count)
            (.index site value) hcursor
        · simp [sourceIndexContinuation220, hsite, hvalue,
            actualChoiceUnknown_spec220, normalizeChoiceResult,
            eraseConsumedHistory_idempotent]
      · simp [sourceIndexContinuation220, hsite, actualChoiceUnknown_spec220,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_index_erased_history_independent220 (t : Tape)
    (site : ExecutionChoices.IndexSite) (count : Nat) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.index tapeAccess site count).run t) =
      normalizeChoiceResult ((ExecutionChoices.index tapeAccess site count).run (eraseConsumedHistory t)) := by
  rw [public_index_eq_source_spec220]
  have hpolicy' : (eraseConsumedHistory t).policy = .strict := by
    simpa [eraseConsumedHistory, compactInputs] using hpolicy
  cases count with
  | zero =>
      simp [sourceIndex220, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | succ n =>
      have hd := strict_demand_bind_spec220 t (ExecutionChoices.Request.index site (Nat.succ n))
        (sourceIndexContinuation220 site (Nat.succ n)) hpolicy
      have hd' := strict_demand_bind_spec220 (eraseConsumedHistory t)
        (ExecutionChoices.Request.index site (Nat.succ n))
        (sourceIndexContinuation220 site (Nat.succ n)) hpolicy'
      have hbeq : (Nat.succ n == 0) = false := rfl
      simp only [sourceIndex220, hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [hd, hd']
      have hlookup : (eraseConsumedHistory t).inputs[(eraseConsumedHistory t).cursor]? =
          t.inputs[t.cursor]? := erase_firstInput_general t
      unfold strictDemandSpec
      rw [hlookup]
      cases hinput : t.inputs[t.cursor]? with
      | none =>
          simp [normalizeChoiceResult, eraseConsumedHistory_idempotent]
      | some input =>
          have hlt : t.cursor < t.inputs.size :=
            (Array.getElem?_eq_some_iff.mp hinput).choose
          exact sourceIndexContinuation_erased220 t site (Nat.succ n) input (Nat.le_of_lt hlt)

theorem strict_bind_erased_history_independent220 {α : Type} (t : Tape)
    (request : ExecutionChoices.Request)
    (continuation : ExecutionChoices.Input → ExecutionChoices.M Tape α)
    (hpolicy : t.policy = .strict)
    (hcontinuation : ∀ input, ∀ state, state.cursor ≤ state.inputs.size →
      normalizeChoiceResult ((continuation input).run state) =
        normalizeChoiceResult ((continuation input).run (eraseConsumedHistory state))) :
    normalizeChoiceResult ((actualChoiceDemand206 tapeAccess request >>= continuation).run t) =
      normalizeChoiceResult ((actualChoiceDemand206 tapeAccess request >>= continuation).run (eraseConsumedHistory t)) := by
  have hpolicy' : (eraseConsumedHistory t).policy = .strict := by
    simpa [eraseConsumedHistory, compactInputs] using hpolicy
  have hd := strict_demand_bind_spec220 t request continuation hpolicy
  have hd' := strict_demand_bind_spec220 (eraseConsumedHistory t) request continuation hpolicy'
  rw [hd, hd']
  have hlookup : (eraseConsumedHistory t).inputs[(eraseConsumedHistory t).cursor]? =
      t.inputs[t.cursor]? := erase_firstInput_general t
  unfold strictDemandSpec
  rw [hlookup]
  cases hinput : t.inputs[t.cursor]? with
  | none => simp [normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | some input =>
      have hlt : t.cursor < t.inputs.size :=
        (Array.getElem?_eq_some_iff.mp hinput).choose
      exact hcontinuation input t (Nat.le_of_lt hlt)

def sourceBooleanContinuation220 (site : ExecutionChoices.BoolSite)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Bool := do
  let .boolean actual value := input | actualChoiceUnknown220 s!"expected Boolean at {repr site}"
  unless actual == site do actualChoiceUnknown220 s!"Boolean site mismatch at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.boolean site) input
  pure value

def sourceBoolean220 (site : ExecutionChoices.BoolSite) : ExecutionChoices.M Tape Bool := do
  let request := ExecutionChoices.Request.boolean site
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBooleanContinuation220 site input

theorem public_boolean_eq_source_spec220 (site : ExecutionChoices.BoolSite) :
    ExecutionChoices.boolean tapeAccess site = sourceBoolean220 site := rfl

theorem sourceBooleanContinuation_erased220 (t : Tape) (site : ExecutionChoices.BoolSite)
    (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBooleanContinuation220 site input).run t) =
      normalizeChoiceResult ((sourceBooleanContinuation220 site input).run (eraseConsumedHistory t)) := by
  cases input with
  | boolean actual value =>
      by_cases hsite : actual = site
      · simp [sourceBooleanContinuation220, hsite, actualChoiceConsume_map_spec220,
          normalizeChoiceResult]
        exact erase_history_after_actual_consume t (ExecutionChoices.Request.boolean site)
          (.boolean site value) hcursor
      · simp [sourceBooleanContinuation220, hsite, actualChoiceUnknown_spec220,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_boolean_erased_history_independent220 (t : Tape)
    (site : ExecutionChoices.BoolSite) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.boolean tapeAccess site).run t) =
      normalizeChoiceResult ((ExecutionChoices.boolean tapeAccess site).run (eraseConsumedHistory t)) := by
  rw [public_boolean_eq_source_spec220]
  change normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation220 site).run t) =
    normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation220 site).run (eraseConsumedHistory t))
  exact strict_bind_erased_history_independent220 t (ExecutionChoices.Request.boolean site)
    (sourceBooleanContinuation220 site) hpolicy
    (fun input state hcursor => sourceBooleanContinuation_erased220 state site input hcursor)

def sourceIntegerContinuation220 (site : ExecutionChoices.IntegerSite) (lower upper : Int)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Int := do
  let .integer actual value := input | actualChoiceUnknown220 s!"expected integer at {repr site}"
  unless actual == site do actualChoiceUnknown220 s!"integer site mismatch at {repr site}"
  unless lower <= value && value <= upper do actualChoiceUnknown220 s!"integer outside support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.integer site lower upper) input
  pure value

def sourceInteger220 (site : ExecutionChoices.IntegerSite) (lower upper : Int) :
    ExecutionChoices.M Tape Int := do
  if lower > upper then throw (.invalidProgram "source random integer range is empty")
  let request := ExecutionChoices.Request.integer site lower upper
  let input ← actualChoiceDemand206 tapeAccess request
  sourceIntegerContinuation220 site lower upper input

theorem public_integer_eq_source_spec220 (site : ExecutionChoices.IntegerSite) (lower upper : Int) :
    ExecutionChoices.integer tapeAccess site lower upper = sourceInteger220 site lower upper := rfl

theorem sourceIntegerContinuation_erased220 (t : Tape) (site : ExecutionChoices.IntegerSite)
    (lower upper : Int) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceIntegerContinuation220 site lower upper input).run t) =
      normalizeChoiceResult ((sourceIntegerContinuation220 site lower upper input).run (eraseConsumedHistory t)) := by
  cases input with
  | integer actual value =>
      cases actual
      cases site
      by_cases hlo : lower ≤ value
      · by_cases hhi : value ≤ upper
        · simp [sourceIntegerContinuation220, hlo, hhi,
            actualChoiceConsume_map_spec220, normalizeChoiceResult]
          exact erase_history_after_actual_consume t
            (ExecutionChoices.Request.integer ExecutionChoices.IntegerSite.floatUlp lower upper)
            (.integer ExecutionChoices.IntegerSite.floatUlp value) hcursor
        · simp [sourceIntegerContinuation220, hlo, hhi,
            actualChoiceUnknown_spec220, normalizeChoiceResult, eraseConsumedHistory_idempotent]
      · simp [sourceIntegerContinuation220, hlo,
          actualChoiceUnknown_spec220, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_integer_erased_history_independent220 (t : Tape)
    (site : ExecutionChoices.IntegerSite) (lower upper : Int) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.integer tapeAccess site lower upper).run t) =
      normalizeChoiceResult ((ExecutionChoices.integer tapeAccess site lower upper).run (eraseConsumedHistory t)) := by
  rw [public_integer_eq_source_spec220]
  by_cases hrange : lower > upper
  · simp [sourceInteger220, hrange, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  · have hnotrange : ¬ lower > upper := hrange
    simp only [sourceInteger220, if_neg hnotrange]
    change normalizeChoiceResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation220 site lower upper).run t) =
      normalizeChoiceResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation220 site lower upper).run (eraseConsumedHistory t))
    exact strict_bind_erased_history_independent220 t
      (ExecutionChoices.Request.integer site lower upper)
      (sourceIntegerContinuation220 site lower upper) hpolicy
      (fun input state hcursor => sourceIntegerContinuation_erased220 state site lower upper input hcursor)

def sourceBytesContinuation220 (site : ExecutionChoices.ByteSite) (length : Nat)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape ByteArray := do
  let .bytes actual value := input | actualChoiceUnknown220 s!"expected bytes at {repr site}"
  unless actual == site do actualChoiceUnknown220 s!"byte site mismatch at {repr site}"
  unless value.size == length do actualChoiceUnknown220 s!"byte vector length mismatch at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.bytes site length) input
  pure ⟨value⟩

def sourceBytes220 (site : ExecutionChoices.ByteSite) (length : Nat) :
    ExecutionChoices.M Tape ByteArray := do
  let request := ExecutionChoices.Request.bytes site length
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBytesContinuation220 site length input

theorem public_bytes_eq_source_spec220 (site : ExecutionChoices.ByteSite) (length : Nat) :
    ExecutionChoices.bytes tapeAccess site length = sourceBytes220 site length := rfl

theorem sourceBytesContinuation_erased220 (t : Tape) (site : ExecutionChoices.ByteSite)
    (length : Nat) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBytesContinuation220 site length input).run t) =
      normalizeChoiceResult ((sourceBytesContinuation220 site length input).run (eraseConsumedHistory t)) := by
  cases input with
  | bytes actual value =>
      cases actual
      cases site
      cases hsize : (value.size == length) with
      | false =>
          simp [sourceBytesContinuation220, hsize, actualChoiceUnknown_spec220,
            normalizeChoiceResult, eraseConsumedHistory_idempotent]
      | true =>
          simp [sourceBytesContinuation220, hsize, actualChoiceConsume_map_spec220,
            normalizeChoiceResult]
          exact erase_history_after_actual_consume t
            (ExecutionChoices.Request.bytes ExecutionChoices.ByteSite.osRandom length)
            (.bytes ExecutionChoices.ByteSite.osRandom value) hcursor
  | index actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_bytes_erased_history_independent220 (t : Tape)
    (site : ExecutionChoices.ByteSite) (length : Nat) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.bytes tapeAccess site length).run t) =
      normalizeChoiceResult ((ExecutionChoices.bytes tapeAccess site length).run (eraseConsumedHistory t)) := by
  rw [public_bytes_eq_source_spec220]
  change normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation220 site length).run t) =
    normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation220 site length).run (eraseConsumedHistory t))
  exact strict_bind_erased_history_independent220 t
    (ExecutionChoices.Request.bytes site length) (sourceBytesContinuation220 site length) hpolicy
    (fun input state hcursor => sourceBytesContinuation_erased220 state site length input hcursor)

theorem state_throw_bind_skip220 {α β : Type} (error : StepError)
    (continuation : α → ExecutionChoices.M Tape β) (state : Tape) :
    ((throw error >>= continuation) state) = .error error state := by
  change EStateM.bind (throw error) continuation state = _
  simp [EStateM.bind, throw_apply_206]

def sourceBernoulliContinuation220 (site : ExecutionChoices.BoolSite) (rateBits : UInt64)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Bool := do
  let .boolean actual value := input | actualChoiceUnknown220 s!"expected probability outcome at {repr site}"
  unless actual == site do actualChoiceUnknown220 s!"probability site mismatch at {repr site}"
  let allowed ← match TerminatorMachine.permitsPreemption rateBits value with
    | .ok allowed => pure allowed
    | .error error => throw error
  unless allowed do actualChoiceUnknown220 s!"Boolean outside probability support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) input
  pure value

def sourceBernoulli220 (site : ExecutionChoices.BoolSite) (rateBits : UInt64) :
    ExecutionChoices.M Tape Bool := do
  let _ ← match TerminatorMachine.permitsPreemption rateBits false with
    | .ok permitted => pure permitted
    | .error error => throw error
  let request := ExecutionChoices.Request.bernoulli site rateBits
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBernoulliContinuation220 site rateBits input

theorem public_bernoulli_eq_source_spec220 (site : ExecutionChoices.BoolSite) (rateBits : UInt64) :
    ExecutionChoices.bernoulli tapeAccess site rateBits = sourceBernoulli220 site rateBits := rfl

theorem sourceBernoulliContinuation_erased220 (t : Tape) (site : ExecutionChoices.BoolSite)
    (rateBits : UInt64) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBernoulliContinuation220 site rateBits input).run t) =
      normalizeChoiceResult ((sourceBernoulliContinuation220 site rateBits input).run (eraseConsumedHistory t)) := by
  cases input with
  | boolean actual value =>
      by_cases hsite : actual = site
      · cases hallowed : TerminatorMachine.permitsPreemption rateBits value with
        | error error =>
            simp [sourceBernoulliContinuation220, hsite, hallowed,
              normalizeChoiceResult, eraseConsumedHistory_idempotent,
              EStateM.bind, EStateM.run, throw_apply_206, state_throw_bind_skip220]
        | ok allowed =>
            cases allowed with
            | false =>
                simp [sourceBernoulliContinuation220, hsite, hallowed,
                  actualChoiceUnknown_spec220, normalizeChoiceResult, eraseConsumedHistory_idempotent]
            | true =>
                simp [sourceBernoulliContinuation220, hsite, hallowed,
                  actualChoiceConsume_map_spec220, normalizeChoiceResult]
                exact erase_history_after_actual_consume t
                  (ExecutionChoices.Request.bernoulli site rateBits) (.boolean site value) hcursor
      · simp [sourceBernoulliContinuation220, hsite, actualChoiceUnknown_spec220,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_bernoulli_erased_history_independent220 (t : Tape)
    (site : ExecutionChoices.BoolSite) (rateBits : UInt64) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run t) =
      normalizeChoiceResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run (eraseConsumedHistory t)) := by
  rw [public_bernoulli_eq_source_spec220]
  cases hpre : TerminatorMachine.permitsPreemption rateBits false with
  | error error =>
      simp [sourceBernoulli220, hpre, normalizeChoiceResult,
        eraseConsumedHistory_idempotent, EStateM.bind, EStateM.pure, EStateM.run,
        throw_apply_206, state_throw_bind_skip220]
  | ok permitted =>
      simp only [sourceBernoulli220, hpre]
      change normalizeChoiceResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation220 site rateBits).run t) =
        normalizeChoiceResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation220 site rateBits).run (eraseConsumedHistory t))
      exact strict_bind_erased_history_independent220 t
        (ExecutionChoices.Request.bernoulli site rateBits) (sourceBernoulliContinuation220 site rateBits)
        hpolicy (fun input state hcursor =>
          sourceBernoulliContinuation_erased220 state site rateBits input hcursor)

#print axioms actualChoiceUnknown_spec220
#print axioms actualChoiceConsume_map_spec220
#print axioms strict_bind_erased_history_independent220
#print axioms state_throw_bind_skip220
#print axioms public_index_erased_history_independent220
#print axioms public_boolean_erased_history_independent220
#print axioms public_bernoulli_erased_history_independent220
#print axioms public_integer_erased_history_independent220
#print axioms public_bytes_erased_history_independent220

/- The locality skeleton is intentionally stronger than consumed-history
normalization: it removes the entire supplied word, including its unread tail,
along with cursor/event bookkeeping, while retaining policy and diagnostic
state. It is used only to compare one wrapper result at a time. -/
def localitySkeleton (t : Tape) : Tape :=
  { t with inputs := #[], cursor := 0, events := #[] }

def normalizeLocalityResult {α : Type} (r : Result α) : Result α :=
  match r with
  | .ok value tape => .ok value (localitySkeleton tape)
  | .error error tape => .error error (localitySkeleton tape)

def strictHeadTape (base : Tape) (current : ExecutionChoices.Input)
    (tail : Array ExecutionChoices.Input) : Tape :=
  { base with inputs := #[current] ++ tail, cursor := 0, policy := .strict, events := #[] }

theorem localitySkeleton_consumed_eq (base : Tape)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input)
    (request : ExecutionChoices.Request) (input : ExecutionChoices.Input) :
    localitySkeleton (consumed (strictHeadTape base current tail₁) request input) =
      localitySkeleton (consumed (strictHeadTape base current tail₂) request input) := by
  cases base with
  | mk inputs cursor policy generatedChoices diagnosticRngState events => rfl

theorem localitySkeleton_headTape_eq (base : Tape)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    localitySkeleton (strictHeadTape base current tail₁) =
      localitySkeleton (strictHeadTape base current tail₂) := by
  cases base with
  | mk inputs cursor policy generatedChoices diagnosticRngState events => rfl

theorem locality_head_demand_bind {α : Type} (base : Tape)
    (current : ExecutionChoices.Input) (tail : Array ExecutionChoices.Input)
    (request : ExecutionChoices.Request)
    (continuation : ExecutionChoices.Input → ExecutionChoices.M Tape α) :
    normalizeLocalityResult
        ((actualChoiceDemand206 tapeAccess request >>= continuation).run
          (strictHeadTape base current tail)) =
      normalizeLocalityResult
        ((continuation current).run (strictHeadTape base current tail)) := by
  have hpolicy : (strictHeadTape base current tail).policy = .strict := rfl
  rw [strict_demand_bind_spec220 _ request continuation hpolicy]
  simp [strictDemandSpec, strictHeadTape, Array.getElem?_append]

theorem sourceIndexContinuation_head_locality220 (base : Tape)
    (site : ExecutionChoices.IndexSite) (count : Nat)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((sourceIndexContinuation220 site count current).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((sourceIndexContinuation220 site count current).run
      (strictHeadTape base current tail₂)) := by
  cases current with
  | index actual value =>
      by_cases hsite : actual = site
      · by_cases hvalue : value < count
        · simp [sourceIndexContinuation220, hsite, hvalue,
            actualChoiceConsume_map_spec220, normalizeLocalityResult,
            localitySkeleton, consumed, strictHeadTape]
        · simp [sourceIndexContinuation220, hsite, hvalue,
            actualChoiceUnknown_spec220, normalizeLocalityResult,
            localitySkeleton, strictHeadTape]
      · simp [sourceIndexContinuation220, hsite, actualChoiceUnknown_spec220,
          normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | boolean actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | integer actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | bytes actual value =>
      simp [sourceIndexContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]

theorem public_index_current_head_locality220 (base : Tape)
    (site : ExecutionChoices.IndexSite) (count : Nat)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((ExecutionChoices.index tapeAccess site count).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((ExecutionChoices.index tapeAccess site count).run
      (strictHeadTape base current tail₂)) := by
  rw [public_index_eq_source_spec220]
  cases count with
  | zero =>
      simp [sourceIndex220, normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | succ n =>
      have hbeq : (Nat.succ n == 0) = false := rfl
      simp only [sourceIndex220, hbeq, Bool.false_eq_true, ↓reduceIte]
      rw [locality_head_demand_bind, locality_head_demand_bind]
      exact sourceIndexContinuation_head_locality220 base site (Nat.succ n)
        current tail₁ tail₂

theorem sourceBooleanContinuation_head_locality220 (base : Tape)
    (site : ExecutionChoices.BoolSite) (current : ExecutionChoices.Input)
    (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((sourceBooleanContinuation220 site current).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((sourceBooleanContinuation220 site current).run
      (strictHeadTape base current tail₂)) := by
  cases current with
  | boolean actual value =>
      by_cases hsite : actual = site
      · simp [sourceBooleanContinuation220, hsite,
          actualChoiceConsume_map_spec220, normalizeLocalityResult,
          localitySkeleton, consumed, strictHeadTape]
      · simp [sourceBooleanContinuation220, hsite, actualChoiceUnknown_spec220,
          normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | index actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | integer actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | bytes actual value =>
      simp [sourceBooleanContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]

theorem public_boolean_current_head_locality220 (base : Tape)
    (site : ExecutionChoices.BoolSite) (current : ExecutionChoices.Input)
    (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((ExecutionChoices.boolean tapeAccess site).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((ExecutionChoices.boolean tapeAccess site).run
      (strictHeadTape base current tail₂)) := by
  rw [public_boolean_eq_source_spec220]
  change normalizeLocalityResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation220 site).run (strictHeadTape base current tail₁)) =
    normalizeLocalityResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation220 site).run (strictHeadTape base current tail₂))
  rw [locality_head_demand_bind, locality_head_demand_bind]
  exact sourceBooleanContinuation_head_locality220 base site current tail₁ tail₂

theorem sourceIntegerContinuation_head_locality220 (base : Tape)
    (site : ExecutionChoices.IntegerSite) (lower upper : Int)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((sourceIntegerContinuation220 site lower upper current).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((sourceIntegerContinuation220 site lower upper current).run
      (strictHeadTape base current tail₂)) := by
  cases current with
  | integer actual value =>
      cases actual
      cases site
      by_cases hlo : lower ≤ value
      · by_cases hhi : value ≤ upper
        · simp [sourceIntegerContinuation220, hlo, hhi,
            actualChoiceConsume_map_spec220, normalizeLocalityResult,
            localitySkeleton, consumed, strictHeadTape]
        · simp [sourceIntegerContinuation220, hlo, hhi,
            actualChoiceUnknown_spec220, normalizeLocalityResult,
            localitySkeleton, strictHeadTape]
      · simp [sourceIntegerContinuation220, hlo,
          actualChoiceUnknown_spec220, normalizeLocalityResult,
          localitySkeleton, strictHeadTape]
  | index actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | boolean actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | bytes actual value =>
      simp [sourceIntegerContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]

theorem public_integer_current_head_locality220 (base : Tape)
    (site : ExecutionChoices.IntegerSite) (lower upper : Int)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((ExecutionChoices.integer tapeAccess site lower upper).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((ExecutionChoices.integer tapeAccess site lower upper).run
      (strictHeadTape base current tail₂)) := by
  rw [public_integer_eq_source_spec220]
  by_cases hrange : lower > upper
  · simp [sourceInteger220, hrange, normalizeLocalityResult,
      localitySkeleton, strictHeadTape, EStateM.bind, EStateM.run, state_throw_bind_skip220]
  · simp only [sourceInteger220, if_neg hrange]
    change normalizeLocalityResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation220 site lower upper).run (strictHeadTape base current tail₁)) =
      normalizeLocalityResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation220 site lower upper).run (strictHeadTape base current tail₂))
    rw [locality_head_demand_bind, locality_head_demand_bind]
    exact sourceIntegerContinuation_head_locality220 base site lower upper current tail₁ tail₂

theorem sourceBytesContinuation_head_locality220 (base : Tape)
    (site : ExecutionChoices.ByteSite) (length : Nat)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((sourceBytesContinuation220 site length current).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((sourceBytesContinuation220 site length current).run
      (strictHeadTape base current tail₂)) := by
  cases current with
  | bytes actual value =>
      cases actual
      cases site
      cases hsize : (value.size == length) with
      | false =>
          simp [sourceBytesContinuation220, hsize, actualChoiceUnknown_spec220,
            normalizeLocalityResult, localitySkeleton, strictHeadTape]
      | true =>
          simp [sourceBytesContinuation220, hsize, actualChoiceConsume_map_spec220,
            normalizeLocalityResult, localitySkeleton, consumed, strictHeadTape]
  | index actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | boolean actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | integer actual value =>
      simp [sourceBytesContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]

theorem public_bytes_current_head_locality220 (base : Tape)
    (site : ExecutionChoices.ByteSite) (length : Nat)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((ExecutionChoices.bytes tapeAccess site length).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((ExecutionChoices.bytes tapeAccess site length).run
      (strictHeadTape base current tail₂)) := by
  rw [public_bytes_eq_source_spec220]
  change normalizeLocalityResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation220 site length).run (strictHeadTape base current tail₁)) =
    normalizeLocalityResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation220 site length).run (strictHeadTape base current tail₂))
  rw [locality_head_demand_bind, locality_head_demand_bind]
  exact sourceBytesContinuation_head_locality220 base site length current tail₁ tail₂

theorem sourceBernoulliContinuation_head_locality220 (base : Tape)
    (site : ExecutionChoices.BoolSite) (rateBits : UInt64)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((sourceBernoulliContinuation220 site rateBits current).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((sourceBernoulliContinuation220 site rateBits current).run
      (strictHeadTape base current tail₂)) := by
  cases current with
  | boolean actual value =>
      by_cases hsite : actual = site
      · cases hallowed : TerminatorMachine.permitsPreemption rateBits value with
        | error error =>
            simp [sourceBernoulliContinuation220, hsite, hallowed,
              normalizeLocalityResult, localitySkeleton, strictHeadTape,
              EStateM.run, EStateM.bind, throw_apply_206, state_throw_bind_skip220]
        | ok allowed =>
            cases allowed with
            | false =>
                simp [sourceBernoulliContinuation220, hsite, hallowed,
                  actualChoiceUnknown_spec220, normalizeLocalityResult,
                  localitySkeleton, strictHeadTape]
            | true =>
                simp [sourceBernoulliContinuation220, hsite, hallowed,
                  actualChoiceConsume_map_spec220, normalizeLocalityResult,
                  localitySkeleton, consumed, strictHeadTape]
      · simp [sourceBernoulliContinuation220, hsite,
          actualChoiceUnknown_spec220, normalizeLocalityResult,
          localitySkeleton, strictHeadTape]
  | index actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | integer actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]
  | bytes actual value =>
      simp [sourceBernoulliContinuation220, actualChoiceUnknown_spec220,
        normalizeLocalityResult, localitySkeleton, strictHeadTape]

theorem public_bernoulli_current_head_locality220 (base : Tape)
    (site : ExecutionChoices.BoolSite) (rateBits : UInt64)
    (current : ExecutionChoices.Input) (tail₁ tail₂ : Array ExecutionChoices.Input) :
    normalizeLocalityResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run
      (strictHeadTape base current tail₁)) =
    normalizeLocalityResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run
      (strictHeadTape base current tail₂)) := by
  rw [public_bernoulli_eq_source_spec220]
  cases hpre : TerminatorMachine.permitsPreemption rateBits false with
  | error error =>
      simp [sourceBernoulli220, hpre, normalizeLocalityResult,
        localitySkeleton, strictHeadTape, EStateM.bind, EStateM.pure, EStateM.run, throw_apply_206, state_throw_bind_skip220]
  | ok permitted =>
      simp only [sourceBernoulli220, hpre]
      change normalizeLocalityResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation220 site rateBits).run
              (strictHeadTape base current tail₁)) =
        normalizeLocalityResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation220 site rateBits).run
              (strictHeadTape base current tail₂))
      rw [locality_head_demand_bind, locality_head_demand_bind]
      exact sourceBernoulliContinuation_head_locality220 base site rateBits current tail₁ tail₂

#print axioms public_index_current_head_locality220
#print axioms public_boolean_current_head_locality220
#print axioms public_bernoulli_current_head_locality220
#print axioms public_integer_current_head_locality220
#print axioms public_bytes_current_head_locality220

end ChoiceLocality220
