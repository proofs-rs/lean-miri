import Lean
import Miri.Interpreter.ExecutionChoices
open Lean Elab Command Tactic
open Miri.Interpreter
namespace ChoicePublic217
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

elab "defineActualChoiceUnknown217" : command => do
  let name ← findUnique206 ".Miri.Interpreter.ExecutionChoices.unknown"
  let ident := mkIdent name
  let defName := mkIdent `actualChoiceUnknown217
  let command ← `(command| def $defName:ident {S A : Type}
    (message : String) : ExecutionChoices.M S A := $ident message)
  elabCommand command

defineActualChoiceUnknown217

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
    mkIdent `ChoicePublic217.state_get_bind_206,
    mkIdent `ChoicePublic217.pure_apply_206,
    mkIdent `ChoicePublic217.throw_apply_206,
    mkIdent `ChoicePublic217.strictDemandSpec
  ]
  evalTactic (← `(tactic| unfold ChoicePublic217.actualChoiceDemand206))
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

elab "simp_public_choice217" : tactic => do
  let helpers ← [
    ".Miri.Interpreter.ExecutionChoices.demand",
    ".Miri.Interpreter.ExecutionChoices.consume",
    ".Miri.Interpreter.ExecutionChoices.unknown"
  ].mapM findUniqueTactic206
  let helperIds := helpers.toArray.map mkIdent ++ #[
    mkIdent `ChoicePublic217.actual_strict_demand_spec,
    mkIdent `ChoicePublic217.actual_consume_spec,
    mkIdent `ChoicePublic217.state_get_bind_206,
    mkIdent `ChoicePublic217.pure_apply_206,
    mkIdent `ChoicePublic217.throw_apply_206,
    mkIdent `ChoicePublic217.erase_history_after_actual_consume,
    mkIdent `ChoicePublic217.eraseConsumedHistory_idempotent,
    mkIdent `ChoicePublic217.compact_firstInput_general,
    mkIdent `ChoicePublic217.erase_firstInput_general
  ]
  let generated ← `(tactic| simp [
    ChoicePublic217.tapeAccess,
    ChoicePublic217.normalizeChoiceResult,
    ChoicePublic217.eraseConsumedHistory,
    ChoicePublic217.compactInputs,
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


theorem strict_demand_bind_spec217 {α : Type}
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

def sourceIndexContinuation217 (site : ExecutionChoices.IndexSite) (count : Nat)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Nat := do
  let .index actual value := input | actualChoiceUnknown217 s!"expected index at {repr site}"
  unless actual == site do actualChoiceUnknown217 s!"index site mismatch at {repr site}"
  unless value < count do actualChoiceUnknown217 s!"index outside support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.index site count) input
  pure value

def sourceIndex217 (site : ExecutionChoices.IndexSite) (count : Nat) :
    ExecutionChoices.M Tape Nat := do
  if count == 0 then
    throw (.invalidProgram "source random selection has empty support")
  let request := ExecutionChoices.Request.index site count
  let input ← actualChoiceDemand206 tapeAccess request
  sourceIndexContinuation217 site count input

theorem public_index_eq_source_spec217 (site : ExecutionChoices.IndexSite) (count : Nat) :
    ExecutionChoices.index tapeAccess site count = sourceIndex217 site count := rfl

elab "simp_actual_unknown217" : tactic => do
  let name ← findUniqueTactic206 ".Miri.Interpreter.ExecutionChoices.unknown"
  let id := mkIdent name
  evalTactic (← `(tactic| simp [$id:ident, EStateM.run]))

theorem actualChoiceUnknown_spec217 {S A : Type} (message : String) (state : S) :
    (@actualChoiceUnknown217 S A message).run state =
      (EStateM.Result.error (.callback s!"choice input unknown: {message}") state : EStateM.Result StepError S A) := by
  unfold actualChoiceUnknown217
  change (throw (StepError.callback s!"choice input unknown: {message}") : EStateM StepError S A) state = _
  exact throw_apply_206 (StepError.callback s!"choice input unknown: {message}") state

theorem actualChoiceConsume_map_spec217 (t : Tape) (request : ExecutionChoices.Request)
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

theorem sourceIndexContinuation_erased217 (t : Tape) (site : ExecutionChoices.IndexSite)
    (count : Nat) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceIndexContinuation217 site count input).run t) =
      normalizeChoiceResult ((sourceIndexContinuation217 site count input).run (eraseConsumedHistory t)) := by
  cases input with
  | index actual value =>
      by_cases hsite : actual = site
      · by_cases hvalue : value < count
        · simp [sourceIndexContinuation217, hsite, hvalue,
            actualChoiceConsume_map_spec217, normalizeChoiceResult]
          exact erase_history_after_actual_consume t (ExecutionChoices.Request.index site count)
            (.index site value) hcursor
        · simp [sourceIndexContinuation217, hsite, hvalue,
            actualChoiceUnknown_spec217, normalizeChoiceResult,
            eraseConsumedHistory_idempotent]
      · simp [sourceIndexContinuation217, hsite, actualChoiceUnknown_spec217,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceIndexContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceIndexContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceIndexContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_index_erased_history_independent217 (t : Tape)
    (site : ExecutionChoices.IndexSite) (count : Nat) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.index tapeAccess site count).run t) =
      normalizeChoiceResult ((ExecutionChoices.index tapeAccess site count).run (eraseConsumedHistory t)) := by
  rw [public_index_eq_source_spec217]
  have hpolicy' : (eraseConsumedHistory t).policy = .strict := by
    simpa [eraseConsumedHistory, compactInputs] using hpolicy
  cases count with
  | zero =>
      simp [sourceIndex217, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | succ n =>
      have hd := strict_demand_bind_spec217 t (ExecutionChoices.Request.index site (Nat.succ n))
        (sourceIndexContinuation217 site (Nat.succ n)) hpolicy
      have hd' := strict_demand_bind_spec217 (eraseConsumedHistory t)
        (ExecutionChoices.Request.index site (Nat.succ n))
        (sourceIndexContinuation217 site (Nat.succ n)) hpolicy'
      have hbeq : (Nat.succ n == 0) = false := rfl
      simp only [sourceIndex217, hbeq, Bool.false_eq_true, ↓reduceIte]
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
          exact sourceIndexContinuation_erased217 t site (Nat.succ n) input (Nat.le_of_lt hlt)

theorem strict_bind_erased_history_independent217 {α : Type} (t : Tape)
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
  have hd := strict_demand_bind_spec217 t request continuation hpolicy
  have hd' := strict_demand_bind_spec217 (eraseConsumedHistory t) request continuation hpolicy'
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

def sourceBooleanContinuation217 (site : ExecutionChoices.BoolSite)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Bool := do
  let .boolean actual value := input | actualChoiceUnknown217 s!"expected Boolean at {repr site}"
  unless actual == site do actualChoiceUnknown217 s!"Boolean site mismatch at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.boolean site) input
  pure value

def sourceBoolean217 (site : ExecutionChoices.BoolSite) : ExecutionChoices.M Tape Bool := do
  let request := ExecutionChoices.Request.boolean site
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBooleanContinuation217 site input

theorem public_boolean_eq_source_spec217 (site : ExecutionChoices.BoolSite) :
    ExecutionChoices.boolean tapeAccess site = sourceBoolean217 site := rfl

theorem sourceBooleanContinuation_erased217 (t : Tape) (site : ExecutionChoices.BoolSite)
    (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBooleanContinuation217 site input).run t) =
      normalizeChoiceResult ((sourceBooleanContinuation217 site input).run (eraseConsumedHistory t)) := by
  cases input with
  | boolean actual value =>
      by_cases hsite : actual = site
      · simp [sourceBooleanContinuation217, hsite, actualChoiceConsume_map_spec217,
          normalizeChoiceResult]
        exact erase_history_after_actual_consume t (ExecutionChoices.Request.boolean site)
          (.boolean site value) hcursor
      · simp [sourceBooleanContinuation217, hsite, actualChoiceUnknown_spec217,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceBooleanContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBooleanContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceBooleanContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_boolean_erased_history_independent217 (t : Tape)
    (site : ExecutionChoices.BoolSite) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.boolean tapeAccess site).run t) =
      normalizeChoiceResult ((ExecutionChoices.boolean tapeAccess site).run (eraseConsumedHistory t)) := by
  rw [public_boolean_eq_source_spec217]
  change normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation217 site).run t) =
    normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.boolean site) >>=
        sourceBooleanContinuation217 site).run (eraseConsumedHistory t))
  exact strict_bind_erased_history_independent217 t (ExecutionChoices.Request.boolean site)
    (sourceBooleanContinuation217 site) hpolicy
    (fun input state hcursor => sourceBooleanContinuation_erased217 state site input hcursor)

def sourceIntegerContinuation217 (site : ExecutionChoices.IntegerSite) (lower upper : Int)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Int := do
  let .integer actual value := input | actualChoiceUnknown217 s!"expected integer at {repr site}"
  unless actual == site do actualChoiceUnknown217 s!"integer site mismatch at {repr site}"
  unless lower <= value && value <= upper do actualChoiceUnknown217 s!"integer outside support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.integer site lower upper) input
  pure value

def sourceInteger217 (site : ExecutionChoices.IntegerSite) (lower upper : Int) :
    ExecutionChoices.M Tape Int := do
  if lower > upper then throw (.invalidProgram "source random integer range is empty")
  let request := ExecutionChoices.Request.integer site lower upper
  let input ← actualChoiceDemand206 tapeAccess request
  sourceIntegerContinuation217 site lower upper input

theorem public_integer_eq_source_spec217 (site : ExecutionChoices.IntegerSite) (lower upper : Int) :
    ExecutionChoices.integer tapeAccess site lower upper = sourceInteger217 site lower upper := rfl

theorem sourceIntegerContinuation_erased217 (t : Tape) (site : ExecutionChoices.IntegerSite)
    (lower upper : Int) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceIntegerContinuation217 site lower upper input).run t) =
      normalizeChoiceResult ((sourceIntegerContinuation217 site lower upper input).run (eraseConsumedHistory t)) := by
  cases input with
  | integer actual value =>
      cases actual
      cases site
      by_cases hlo : lower ≤ value
      · by_cases hhi : value ≤ upper
        · simp [sourceIntegerContinuation217, hlo, hhi,
            actualChoiceConsume_map_spec217, normalizeChoiceResult]
          exact erase_history_after_actual_consume t
            (ExecutionChoices.Request.integer ExecutionChoices.IntegerSite.floatUlp lower upper)
            (.integer ExecutionChoices.IntegerSite.floatUlp value) hcursor
        · simp [sourceIntegerContinuation217, hlo, hhi,
            actualChoiceUnknown_spec217, normalizeChoiceResult, eraseConsumedHistory_idempotent]
      · simp [sourceIntegerContinuation217, hlo,
          actualChoiceUnknown_spec217, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceIntegerContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceIntegerContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceIntegerContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_integer_erased_history_independent217 (t : Tape)
    (site : ExecutionChoices.IntegerSite) (lower upper : Int) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.integer tapeAccess site lower upper).run t) =
      normalizeChoiceResult ((ExecutionChoices.integer tapeAccess site lower upper).run (eraseConsumedHistory t)) := by
  rw [public_integer_eq_source_spec217]
  by_cases hrange : lower > upper
  · simp [sourceInteger217, hrange, normalizeChoiceResult, eraseConsumedHistory_idempotent]
  · have hnotrange : ¬ lower > upper := hrange
    simp only [sourceInteger217, if_neg hnotrange]
    change normalizeChoiceResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation217 site lower upper).run t) =
      normalizeChoiceResult
        ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.integer site lower upper) >>=
          sourceIntegerContinuation217 site lower upper).run (eraseConsumedHistory t))
    exact strict_bind_erased_history_independent217 t
      (ExecutionChoices.Request.integer site lower upper)
      (sourceIntegerContinuation217 site lower upper) hpolicy
      (fun input state hcursor => sourceIntegerContinuation_erased217 state site lower upper input hcursor)

def sourceBytesContinuation217 (site : ExecutionChoices.ByteSite) (length : Nat)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape ByteArray := do
  let .bytes actual value := input | actualChoiceUnknown217 s!"expected bytes at {repr site}"
  unless actual == site do actualChoiceUnknown217 s!"byte site mismatch at {repr site}"
  unless value.size == length do actualChoiceUnknown217 s!"byte vector length mismatch at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.bytes site length) input
  pure ⟨value⟩

def sourceBytes217 (site : ExecutionChoices.ByteSite) (length : Nat) :
    ExecutionChoices.M Tape ByteArray := do
  let request := ExecutionChoices.Request.bytes site length
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBytesContinuation217 site length input

theorem public_bytes_eq_source_spec217 (site : ExecutionChoices.ByteSite) (length : Nat) :
    ExecutionChoices.bytes tapeAccess site length = sourceBytes217 site length := rfl

theorem sourceBytesContinuation_erased217 (t : Tape) (site : ExecutionChoices.ByteSite)
    (length : Nat) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBytesContinuation217 site length input).run t) =
      normalizeChoiceResult ((sourceBytesContinuation217 site length input).run (eraseConsumedHistory t)) := by
  cases input with
  | bytes actual value =>
      cases actual
      cases site
      cases hsize : (value.size == length) with
      | false =>
          simp [sourceBytesContinuation217, hsize, actualChoiceUnknown_spec217,
            normalizeChoiceResult, eraseConsumedHistory_idempotent]
      | true =>
          simp [sourceBytesContinuation217, hsize, actualChoiceConsume_map_spec217,
            normalizeChoiceResult]
          exact erase_history_after_actual_consume t
            (ExecutionChoices.Request.bytes ExecutionChoices.ByteSite.osRandom length)
            (.bytes ExecutionChoices.ByteSite.osRandom value) hcursor
  | index actual value =>
      simp [sourceBytesContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | boolean actual value =>
      simp [sourceBytesContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBytesContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_bytes_erased_history_independent217 (t : Tape)
    (site : ExecutionChoices.ByteSite) (length : Nat) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.bytes tapeAccess site length).run t) =
      normalizeChoiceResult ((ExecutionChoices.bytes tapeAccess site length).run (eraseConsumedHistory t)) := by
  rw [public_bytes_eq_source_spec217]
  change normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation217 site length).run t) =
    normalizeChoiceResult
      ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bytes site length) >>=
        sourceBytesContinuation217 site length).run (eraseConsumedHistory t))
  exact strict_bind_erased_history_independent217 t
    (ExecutionChoices.Request.bytes site length) (sourceBytesContinuation217 site length) hpolicy
    (fun input state hcursor => sourceBytesContinuation_erased217 state site length input hcursor)

theorem state_throw_bind_skip217 {α β : Type} (error : StepError)
    (continuation : α → ExecutionChoices.M Tape β) (state : Tape) :
    ((throw error >>= continuation) state) = .error error state := by
  change EStateM.bind (throw error) continuation state = _
  simp [EStateM.bind, throw_apply_206]

def sourceBernoulliContinuation217 (site : ExecutionChoices.BoolSite) (rateBits : UInt64)
    (input : ExecutionChoices.Input) : ExecutionChoices.M Tape Bool := do
  let .boolean actual value := input | actualChoiceUnknown217 s!"expected probability outcome at {repr site}"
  unless actual == site do actualChoiceUnknown217 s!"probability site mismatch at {repr site}"
  let allowed ← match TerminatorMachine.permitsPreemption rateBits value with
    | .ok allowed => pure allowed
    | .error error => throw error
  unless allowed do actualChoiceUnknown217 s!"Boolean outside probability support at {repr site}"
  actualChoiceConsume206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) input
  pure value

def sourceBernoulli217 (site : ExecutionChoices.BoolSite) (rateBits : UInt64) :
    ExecutionChoices.M Tape Bool := do
  let _ ← match TerminatorMachine.permitsPreemption rateBits false with
    | .ok permitted => pure permitted
    | .error error => throw error
  let request := ExecutionChoices.Request.bernoulli site rateBits
  let input ← actualChoiceDemand206 tapeAccess request
  sourceBernoulliContinuation217 site rateBits input

theorem public_bernoulli_eq_source_spec217 (site : ExecutionChoices.BoolSite) (rateBits : UInt64) :
    ExecutionChoices.bernoulli tapeAccess site rateBits = sourceBernoulli217 site rateBits := rfl

theorem sourceBernoulliContinuation_erased217 (t : Tape) (site : ExecutionChoices.BoolSite)
    (rateBits : UInt64) (input : ExecutionChoices.Input) (hcursor : t.cursor ≤ t.inputs.size) :
    normalizeChoiceResult ((sourceBernoulliContinuation217 site rateBits input).run t) =
      normalizeChoiceResult ((sourceBernoulliContinuation217 site rateBits input).run (eraseConsumedHistory t)) := by
  cases input with
  | boolean actual value =>
      by_cases hsite : actual = site
      · cases hallowed : TerminatorMachine.permitsPreemption rateBits value with
        | error error =>
            simp [sourceBernoulliContinuation217, hsite, hallowed,
              normalizeChoiceResult, eraseConsumedHistory_idempotent,
              EStateM.bind, EStateM.run, throw_apply_206, state_throw_bind_skip217]
        | ok allowed =>
            cases allowed with
            | false =>
                simp [sourceBernoulliContinuation217, hsite, hallowed,
                  actualChoiceUnknown_spec217, normalizeChoiceResult, eraseConsumedHistory_idempotent]
            | true =>
                simp [sourceBernoulliContinuation217, hsite, hallowed,
                  actualChoiceConsume_map_spec217, normalizeChoiceResult]
                exact erase_history_after_actual_consume t
                  (ExecutionChoices.Request.bernoulli site rateBits) (.boolean site value) hcursor
      · simp [sourceBernoulliContinuation217, hsite, actualChoiceUnknown_spec217,
          normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | index actual value =>
      simp [sourceBernoulliContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | integer actual value =>
      simp [sourceBernoulliContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]
  | bytes actual value =>
      simp [sourceBernoulliContinuation217, actualChoiceUnknown_spec217,
        normalizeChoiceResult, eraseConsumedHistory_idempotent]

theorem public_bernoulli_erased_history_independent217 (t : Tape)
    (site : ExecutionChoices.BoolSite) (rateBits : UInt64) (hpolicy : t.policy = .strict) :
    normalizeChoiceResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run t) =
      normalizeChoiceResult ((ExecutionChoices.bernoulli tapeAccess site rateBits).run (eraseConsumedHistory t)) := by
  rw [public_bernoulli_eq_source_spec217]
  cases hpre : TerminatorMachine.permitsPreemption rateBits false with
  | error error =>
      simp [sourceBernoulli217, hpre, normalizeChoiceResult,
        eraseConsumedHistory_idempotent, EStateM.bind, EStateM.pure, EStateM.run,
        throw_apply_206, state_throw_bind_skip217]
  | ok permitted =>
      simp only [sourceBernoulli217, hpre]
      change normalizeChoiceResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation217 site rateBits).run t) =
        normalizeChoiceResult
          ((actualChoiceDemand206 tapeAccess (ExecutionChoices.Request.bernoulli site rateBits) >>=
            sourceBernoulliContinuation217 site rateBits).run (eraseConsumedHistory t))
      exact strict_bind_erased_history_independent217 t
        (ExecutionChoices.Request.bernoulli site rateBits) (sourceBernoulliContinuation217 site rateBits)
        hpolicy (fun input state hcursor =>
          sourceBernoulliContinuation_erased217 state site rateBits input hcursor)

#print axioms actualChoiceUnknown_spec217
#print axioms actualChoiceConsume_map_spec217
#print axioms strict_bind_erased_history_independent217
#print axioms state_throw_bind_skip217
#print axioms public_index_erased_history_independent217
#print axioms public_boolean_erased_history_independent217
#print axioms public_bernoulli_erased_history_independent217
#print axioms public_integer_erased_history_independent217
#print axioms public_bytes_erased_history_independent217
end ChoicePublic217
