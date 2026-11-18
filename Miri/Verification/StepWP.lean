import Miri.Verification.FunctionBody
import Std.Tactic.Do
import Std.WP

/-! Verification conditions for finite sequences of interpreter steps. Each
step uses the existing driver and quantifies over its permitted choices. -/
namespace Miri.Verification.StepWP

open Miri.Interpreter Miri.MIR
open Std.WP

variable {P L E M C V : Type}
local notation "State" => StepState P L E M
local notation "Hooks" => StepHooks P L E M C V

inductive Instruction where
  | statement (kind : StatementKind)
  | ret
  | goto (target : BasicBlockId) (hints : Array LoopHintAttr)
  | terminator (kind : TerminatorKind)

/-- The terminator selected by the driver, including source information. -/
def currentTerminator (state : State) : Option Terminator := do
  let frame ← state.stack.currentFrame?
  let .mir loc := frame.location | none
  let block ← frame.body.basicBlocks[loc.block]?
  match block.statements[loc.statementIndex]? with
  | some _ => none
  | none => some block.terminator

/-- Check the same frame, block and statement slot that the driver dispatches. -/
def Instruction.matches (instruction : Instruction) (state : State) : Prop :=
  match instruction with
  | .ret => (currentTerminator state).map Terminator.kind = some .Return
  | .goto target hints => (currentTerminator state).map Terminator.kind = some (.Goto target hints)
  | .terminator kind => (currentTerminator state).map Terminator.kind = some kind
  | .statement kind =>
    match state.stack.currentFrame? with
    | some frame =>
      match frame.location with
      | .mir loc =>
        match frame.body.basicBlocks[loc.block]? with
        | some block =>
          match block.statements[loc.statementIndex]? with
          | some stmt => stmt.kind = kind
          | none => False
        | none => False
      | .unwinding _ => False
    | none => False

/-- Each step states the expected driver result: `true` for a step that
continues, `false` for a step that finds an empty stack. -/
inductive Program (hooks : Hooks) (allowed : State → C → Prop) where
  | step (more : Bool)
  | instruction (operation : Instruction)
  | call (prepare : C → State → EStateM.Result StepError State Unit)
  | seq (first next : Program hooks allowed)

variable {hooks : StepHooks P L E M C V} {allowed : StepState P L E M → C → Prop}

/-- The control instructions with a registered driver rule. -/
def lowerTerminator : TerminatorKind → Option Instruction
  | .Return => some .ret
  | .Goto target hints => some (.goto target hints)
  | kind@(.SwitchInt ..) | kind@(.Assert ..) | kind@(.Call ..) | kind@(.Drop ..) =>
    some (.terminator kind)
  | _ => none

/-- Lower a block up to and including its terminator. The postcondition observes
the actual successor state, so branch targets need not be evaluated here. -/
def lowerBlock (block : BasicBlock) : Option (Program hooks allowed) := do
  let last ← lowerTerminator block.terminator.kind
  return block.statements.foldr
    (fun statement next => .seq (.instruction (.statement statement.kind)) next)
    (.instruction last)

/-- Lower a one-block body with a Return terminator. Instruction guards bind
the resulting verification program to the MIR actually stepped. -/
def lowerStraightLine (body : Body) : Option (Program hooks allowed) := do
  let #[block] := body.basicBlocks | none
  let .Return := block.terminator.kind | none
  lowerBlock block

/-- Demand a permitted choice and check every permitted result, retaining the
actual failed state on error. -/
def transitionPre (allowed : State → C → Prop) (more : Bool) (run : C → StepResult State Bool)
    (post : State → Prop) (onError : StepError → State → Prop) (state : State) : Prop :=
  (∃ choice, allowed state choice) ∧
    ∀ choice, allowed state choice →
      match run choice with
      | (after, .ok actual) => actual = more ∧ post after
      | (after, .error error) => onError error after

abbrev stepPre (hooks : Hooks) (allowed : State → C → Prop) (more : Bool)
    (post : State → Prop) (onError : StepError → State → Prop) (state : State) : Prop :=
  transitionPre allowed more (fun choice => Step.step hooks choice state) post onError state

theorem stepPre_outcome {hooks : Hooks} {allowed : State → C → Prop} {more : Bool}
    {post : State → Prop} {onError : StepError → State → Prop} {before after : State}
    {result : Except StepError Bool} (h : stepPre hooks allowed more post onError before)
    (hstep : Step.AllowedStep hooks allowed before after result) :
    match result with
    | .ok actual => actual = more ∧ post after
    | .error error => onError error after := by
  obtain ⟨choice, permitted, outcome⟩ := hstep
  cases result <;> simpa only [outcome] using h.2 choice permitted

/-- A direct call uses the supplied preparation action, then follows real
driver steps until the callee leaves scope. Every successful scope exit must
satisfy `post`, which can require the normal caller continuation. -/
def callPre (hooks : Hooks) (allowed : State → C → Prop)
    (prepare : C → State → EStateM.Result StepError State Unit)
    (post : State → Prop) (onError : StepError → State → Prop) (before : State) : Prop :=
  (∃ choice, allowed before choice) ∧
    ∀ choice, allowed before choice →
      match prepare choice before with
      | .error error failed => onError error failed
      | .ok () entry =>
        let depth := before.stack.frames.size + 1
        let stackDepth := fun state : State => state.stack.frames.size
        stackDepth entry = depth ∧
          FunctionBody.OnError (Step.step hooks) stackDepth allowed depth entry onError ∧
          FunctionBody.NormalPost (Step.step hooks) stackDepth allowed depth entry post

/-- Apply a callee contract to actual preparation. The contract is checked at
every entry produced by a permitted choice; the preparation error is separate. -/
theorem callPre_of_contract {prepare : C → State → EStateM.Result StepError State Unit}
    {post : State → Prop} {onError : StepError → State → Prop} {before : State}
    (enabled : ∃ choice, allowed before choice)
    (prepareError : ∀ choice, allowed before choice → ∀ failed error,
      prepare choice before = .error error failed → onError error failed)
    (prepared : ∀ choice, allowed before choice → ∀ entry, prepare choice before = .ok () entry →
      entry.stack.frames.size = before.stack.frames.size + 1 ∧
      FunctionBody.OnError (Step.step hooks) (fun state => state.stack.frames.size) allowed
        (before.stack.frames.size + 1) entry onError ∧
      FunctionBody.NormalPost (Step.step hooks) (fun state => state.stack.frames.size) allowed
        (before.stack.frames.size + 1) entry post) :
    callPre hooks allowed prepare post onError before := by
  refine ⟨enabled, fun choice permitted => ?_⟩
  cases outcome : prepare choice before with
  | error error failed => exact prepareError choice permitted failed error outcome
  | ok value entry =>
    cases value
    exact prepared choice permitted entry outcome

/-- After each expected successful result, the next command sees the updated state.
Errors go directly to the enclosing error postcondition. -/
def pre : Program hooks allowed → (State → Prop) → (StepError → State → Prop) → State → Prop
  | .step more, post, onError => stepPre hooks allowed more post onError
  | .instruction operation, post, onError =>
    fun state => operation.matches state ∧ stepPre hooks allowed true post onError state
  | .call prepare, post, onError => callPre hooks allowed prepare post onError
  | .seq first next, post, onError => pre first (pre next post onError) onError

theorem stepPre_mono {more : Bool}
    {post post' : State → Prop} {onError onError' : StepError → State → Prop}
    (hpost : ∀ state, post state → post' state)
    (herror : ∀ error state, onError error state → onError' error state)
    (state : State) (h : stepPre hooks allowed more post onError state) :
    stepPre hooks allowed more post' onError' state := by
  refine ⟨h.1, fun choice permitted => ?_⟩
  have hresult := h.2 choice permitted
  cases outcome : Step.step hooks choice state with
  | mk after result =>
    cases result with
    | ok actual =>
      simp only [outcome] at hresult ⊢
      exact ⟨hresult.1, hpost after hresult.2⟩
    | error error =>
      simp only [outcome] at hresult ⊢
      exact herror error after hresult

private theorem pre_mono (program : Program hooks allowed)
    {post post' : State → Prop} {onError onError' : StepError → State → Prop}
    (hpost : ∀ state, post state → post' state)
    (herror : ∀ error state, onError error state → onError' error state) :
    ∀ state, pre program post onError state → pre program post' onError' state := by
  induction program generalizing post post' with
  | step more => exact stepPre_mono hpost herror
  | instruction operation =>
    intro state h
    exact ⟨h.1, stepPre_mono hpost herror state h.2⟩
  | call prepare =>
    intro state h
    refine ⟨h.1, fun choice permitted => ?_⟩
    have actual := h.2 choice permitted
    cases outcome : prepare choice state with
    | error error failed =>
      simp only [outcome] at actual ⊢
      exact herror error failed actual
    | ok value entry =>
      cases value
      simp only [outcome] at actual ⊢
      refine ⟨actual.1, ?_, ?_⟩
      · intro before reached inside c enabled after error failed
        exact herror error after (actual.2.1 before reached inside c enabled after error failed)
      · intro after reached outside
        exact hpost after (actual.2.2 after reached outside)
  | seq first next firstIH nextIH =>
    exact firstIH (nextIH hpost)

instance : WP (Program hooks allowed) Unit (StepState P L E M → Prop)
    (StepError → StepState P L E M → Prop) where
  wpTrans program := ⟨fun post onError => pre program (post ()) onError⟩
  wp_trans_monotone program := by
    intro post post' onError onError' herror hpost
    exact pre_mono program (hpost ()) herror

@[spec] theorem spec_step (hooks : Hooks) (allowed : State → C → Prop) (more : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.step (hooks := hooks) (allowed := allowed) more)
      (stepPre hooks allowed more (post ()) onError) post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

@[spec] theorem spec_seq (first next : Program hooks allowed)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.seq first next) (wp first (fun _ => wp next post onError) onError)
      post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

@[spec low] theorem spec_instruction (hooks : Hooks) (allowed : State → C → Prop)
    (operation : Instruction) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) operation)
      (fun state => operation.matches state ∧ stepPre hooks allowed true (post ()) onError state)
      post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

private theorem statement_at {kind : StatementKind} {before : State}
    (matched : (Instruction.statement kind).matches before) :
    ∃ frame loc block stmt,
      before.stack.currentFrame? = some frame ∧ frame.location = .mir loc ∧
      frame.body.basicBlocks[loc.block]? = some block ∧
      block.statements[loc.statementIndex]? = some stmt ∧ stmt.kind = kind := by
  cases current : before.stack.currentFrame? with
  | none => simp [Instruction.matches, current] at matched
  | some frame =>
    cases pc : frame.location with
    | unwinding => simp [Instruction.matches, current, pc] at matched
    | mir loc =>
      cases found : frame.body.basicBlocks[loc.block]? with
      | none => simp [Instruction.matches, current, pc, found] at matched
      | some block =>
        cases slot : block.statements[loc.statementIndex]? with
        | none => simp [Instruction.matches, current, pc, found, slot] at matched
        | some stmt =>
          exact ⟨frame, loc, block, stmt, rfl, pc, found, slot, by
            simpa [Instruction.matches, current, pc, found, slot] using matched⟩

private theorem terminator_at {before : State} {term : Terminator}
    (selected : currentTerminator before = some term) :
    ∃ frame loc block,
      before.stack.currentFrame? = some frame ∧ frame.location = .mir loc ∧
      frame.body.basicBlocks[loc.block]? = some block ∧
      block.statements[loc.statementIndex]? = none ∧ block.terminator = term := by
  cases current : before.stack.currentFrame? with
  | none => simp [currentTerminator, current] at selected
  | some frame =>
    cases pc : frame.location with
    | unwinding => simp [currentTerminator, current, pc] at selected
    | mir loc =>
      cases found : frame.body.basicBlocks[loc.block]? with
      | none => simp [currentTerminator, current, pc, found] at selected
      | some block =>
        cases slot : block.statements[loc.statementIndex]? with
        | some stmt => simp [currentTerminator, current, pc, found, slot] at selected
        | none =>
          exact ⟨frame, loc, block, rfl, pc, found, slot, by
            simpa [currentTerminator, current, pc, found, slot] using selected⟩

theorem step_eq_runTerminator {before : State} {term : Terminator}
    (selected : currentTerminator before = some term) (hooks : Hooks) (choice : C) :
    Step.step hooks choice before = Step.runTerminator hooks choice term before := by
  obtain ⟨_, _, _, current, pc, found, slot, equal⟩ := terminator_at selected
  simp only [Step.step, current, pc, found, slot, Id.run, pure, Pure.pure, equal]

/-- Replace the newest frame with the same frame at the next statement. -/
def afterNop (state : State) (frame : Frame P L E) (loc : Location) : State :=
  { state with stack := ⟨state.stack.frames.pop.push
      { frame with location := .mir {loc with statementIndex := loc.statementIndex + 1} }⟩ }

@[spec] theorem spec_nop (hooks : Hooks) (allowed : State → C → Prop)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement .Nop))
      (fun before => (Instruction.statement .Nop).matches before ∧
        (∃ choice, allowed before choice) ∧
        ∀ frame loc, before.stack.currentFrame? = some frame →
          frame.location = .mir loc → post () (afterNop before frame loc)) post onError := by
  apply Triple.iff.mpr
  rintro before ⟨matched, enabled, next⟩
  obtain ⟨frame, loc, block, stmt, current, pc, found, slot, kind⟩ := statement_at matched
  have stack : ∃ older : Array (Frame P L E), before.stack.frames = older.push frame :=
    Array.back?_eq_some_iff.mp current
  rcases stack with ⟨older, stack⟩
  refine ⟨matched, enabled, ?_⟩
  intro choice _
  change (match Step.step hooks choice before with
    | (after, .ok more) => more = true ∧ post () after
    | (after, .error error) => onError error after)
  have outcome : Step.step hooks choice before = (afterNop before frame loc, .ok true) := by
    simp [Step.step, Step.evalStatement, current, pc, found, slot, kind, afterNop, stack, Array.set_push]
  rw [outcome]
  exact ⟨rfl, next frame loc current pc⟩

private theorem spec_statement_effect (hooks : Hooks) (allowed : State → C → Prop)
    (kind : StatementKind) (effect : C → State → StepResult State Unit)
    (dispatch : ∀ choice source state,
      Step.evalStatement hooks choice ⟨source, kind⟩ state = effect choice state)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement kind))
      (fun before => (Instruction.statement kind).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1) (effect choice before))
          (post ()) onError before) post onError := by
  apply Triple.iff.mpr
  rintro before ⟨matched, enabled, run⟩
  obtain ⟨_, _, _, stmt, current, pc, found, slot, kindEq⟩ := statement_at matched
  have stmtEq : stmt = ⟨stmt.sourceInfo, kind⟩ := by cases stmt; simp_all
  refine ⟨matched, enabled, ?_⟩
  intro choice permitted
  have outcome : Step.step hooks choice before = Step.finishStatement
      (before.stack.frames.size - 1) (effect choice before) := by
    simp only [Step.step, current, pc, found, slot, Id.run, pure, Pure.pure]
    rw [stmtEq, dispatch]
  simpa only [outcome] using run choice permitted

private theorem successful_statement_depth {kind : StatementKind} {before after : State}
    (choice : C) (matched : (Instruction.statement kind).matches before)
    (outcome : Step.step hooks choice before = (after, .ok true)) :
    after.stack.frames.size = before.stack.frames.size := by
  obtain ⟨frame, _, _, stmt, current, pc, found, slot, _⟩ := statement_at matched
  have nonempty : 0 < before.stack.frames.size := by
    have nonempty : before.stack.frames.back? = some frame := current
    cases h : before.stack.frames.size with
    | zero =>
      rw [show before.stack.frames = #[] from Array.size_eq_zero_iff.mp h] at nonempty
      contradiction
    | succ n => omega
  simp only [Step.step, current, pc, found, slot, Id.run, pure, Pure.pure] at outcome
  rcases executed : Step.evalStatement hooks choice stmt before with ⟨state, result⟩
  rw [executed] at outcome
  cases result with
  | error error => simp at outcome
  | ok value =>
    cases value
    dsimp only at outcome
    split at outcome
    · simp at outcome
    rename_i index
    split at outcome
    · rename_i current hcurrent
      split at outcome
      · split at outcome
        · cases outcome
          simp only [Array.size_set]
          have indices : before.stack.frames.size - 1 = state.stack.frames.size - 1 := by
            simpa using index
          omega
        · simp at outcome
      · simp at outcome
    · simp at outcome

/-- Dispatch the checked assignment to the existing rvalue implementation. -/
theorem step_eq_assign {before : State} {destination : Place} {rhs : Rvalue}
    (matched : (Instruction.statement (.Assign destination rhs)).matches before)
    (hooks : Hooks) (choice : C) :
    Step.step hooks choice before = Step.finishStatement
      (before.stack.frames.size - 1) (hooks.assign choice destination rhs before) := by
  obtain ⟨_, _, _, _, current, pc, found, slot, kind⟩ := statement_at matched
  simp only [Step.step, current, pc, found, slot, Step.evalStatement, kind, Id.run, pure, Pure.pure]

@[spec] theorem spec_assign (hooks : Hooks) (allowed : State → C → Prop)
    (destination : Place) (rhs : Rvalue) (post : Unit → State → Prop)
    (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed)
        (.statement (.Assign destination rhs)))
      (fun before => (Instruction.statement (.Assign destination rhs)).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1)
            (hooks.assign choice destination rhs before)) (post ()) onError before)
      post onError := by
  apply Triple.iff.mpr
  rintro before ⟨matched, enabled, run⟩
  refine ⟨matched, enabled, ?_⟩
  intro choice permitted
  simpa only [step_eq_assign matched hooks choice] using run choice permitted

@[spec] theorem spec_storageLive (hooks : Hooks) (allowed : State → C → Prop)
    (localId : LocalId) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.StorageLive localId)))
      (fun before => (Instruction.statement (.StorageLive localId)).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1)
            (hooks.storageLive choice localId before)) (post ()) onError before)
      post onError :=
  spec_statement_effect hooks allowed (.StorageLive localId) (fun choice => hooks.storageLive choice localId) (by intros; rfl) post onError

@[spec] theorem spec_storageDead (hooks : Hooks) (allowed : State → C → Prop)
    (localId : LocalId) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.StorageDead localId)))
      (fun before => (Instruction.statement (.StorageDead localId)).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1)
            (hooks.storageDead choice localId before)) (post ()) onError before)
      post onError :=
  spec_statement_effect hooks allowed (.StorageDead localId) (fun choice => hooks.storageDead choice localId) (by intros; rfl) post onError

@[spec] theorem spec_placeMention (hooks : Hooks) (allowed : State → C → Prop)
    (place : Place) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.PlaceMention place)))
      (fun before => (Instruction.statement (.PlaceMention place)).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1)
            ((let result := hooks.evalPlace choice place false before
             (result.1, result.2.map fun _ => ())))) (post ()) onError before)
      post onError :=
  spec_statement_effect hooks allowed (.PlaceMention place) (fun choice state =>
    let result := hooks.evalPlace choice place false state
    (result.1, result.2.map fun _ => ())) (by intros; rfl) post onError

@[spec] theorem spec_copyNonOverlapping (hooks : Hooks) (allowed : State → C → Prop)
    (args : CopyNonOverlapping) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.Intrinsic (.CopyNonOverlapping args))))
      (fun before => (Instruction.statement (.Intrinsic (.CopyNonOverlapping args))).matches before ∧
        transitionPre allowed true
          (fun choice => Step.finishStatement (before.stack.frames.size - 1)
            (hooks.intrinsic choice (.CopyNonOverlapping args) before)) (post ()) onError before)
      post onError :=
  spec_statement_effect hooks allowed (.Intrinsic (.CopyNonOverlapping args)) (fun choice => hooks.intrinsic choice (.CopyNonOverlapping args)) (by intros; rfl) post onError

private theorem spec_terminator_of_kind (hooks : Hooks) (allowed : State → C → Prop)
    (instruction : Instruction) (kind : TerminatorKind)
    (dispatch : ∀ state : State, instruction.matches state ↔
      (currentTerminator state).map Terminator.kind = some kind)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) instruction)
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = kind ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError := by
  apply Triple.iff.mpr
  rintro before ⟨term, selected, kindEq, enabled, run⟩
  have matched : instruction.matches before := (dispatch before).mpr (by
    simp only [selected, Option.map_some, kindEq])
  refine ⟨matched, enabled, ?_⟩
  intro choice permitted
  simpa only [step_eq_runTerminator selected hooks choice] using run choice permitted

@[spec] theorem spec_return (hooks : Hooks) (allowed : State → C → Prop)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) .ret)
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .Return ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed .ret .Return (fun _ => Iff.rfl) post onError

@[spec] theorem spec_goto (hooks : Hooks) (allowed : State → C → Prop)
    (target : BasicBlockId) (hints : Array LoopHintAttr)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.goto target hints))
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .Goto target hints ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed (.goto target hints) (.Goto target hints)
    (fun _ => Iff.rfl) post onError

@[spec] theorem spec_switchInt (hooks : Hooks) (allowed : State → C → Prop)
    (discriminant : Operand) (targets : SwitchTargets) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed)
        (.terminator (.SwitchInt discriminant targets)))
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .SwitchInt discriminant targets ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed (.terminator (.SwitchInt discriminant targets))
    (.SwitchInt discriminant targets) (fun _ => Iff.rfl) post onError

@[spec] theorem spec_assert (hooks : Hooks) (allowed : State → C → Prop)
    (condition : Operand) (expected : Bool) (message : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed)
        (.terminator (.Assert condition expected message target unwind)))
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .Assert condition expected message target unwind ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed (.terminator (.Assert condition expected message target unwind))
    (.Assert condition expected message target unwind) (fun _ => Iff.rfl) post onError

@[spec] theorem spec_callTerminator (hooks : Hooks) (allowed : State → C → Prop)
    (callee : Operand) (args : Array SpannedOperand) (destination : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) (source : CallSource) (span : SpanRef) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed)
        (.terminator (.Call callee args destination target unwind source span)))
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .Call callee args destination target unwind source span ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed (.terminator (.Call callee args destination target unwind source span))
    (.Call callee args destination target unwind source span) (fun _ => Iff.rfl) post onError

@[spec] theorem spec_drop (hooks : Hooks) (allowed : State → C → Prop)
    (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
    (replace : Bool) (asyncDrop : Option BasicBlockId) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed)
        (.terminator (.Drop place target unwind replace asyncDrop)))
      (fun before => ∃ term, currentTerminator before = some term ∧ term.kind = .Drop place target unwind replace asyncDrop ∧
        transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
          (post ()) onError before) post onError :=
  spec_terminator_of_kind hooks allowed (.terminator (.Drop place target unwind replace asyncDrop))
    (.Drop place target unwind replace asyncDrop) (fun _ => Iff.rfl) post onError

@[spec] theorem spec_call (hooks : Hooks) (allowed : State → C → Prop)
    (prepare : C → State → EStateM.Result StepError State Unit)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (Program.call (hooks := hooks) (allowed := allowed) prepare)
      (callPre hooks allowed prepare (post ()) onError) post onError :=
  Triple.iff.mpr (by intro _ h; exact h)

/-- Nonempty suffixes of a lowered block, with all statements before its
terminator. Keeping the suffix accounts for errors at intermediate PCs. -/
private inductive BlockSuffix : Program hooks allowed → Prop where
  | last (instruction : Instruction) : BlockSuffix (.instruction instruction)
  | statement (kind : StatementKind) {rest : Program hooks allowed} :
      BlockSuffix rest → BlockSuffix (.seq (.instruction (.statement kind)) rest)

private theorem lowered_suffix {block : BasicBlock} {program : Program hooks allowed}
    (lowered : lowerBlock block = some program) : BlockSuffix program := by
  unfold lowerBlock at lowered
  cases last : lowerTerminator block.terminator.kind with
  | none => simp [last] at lowered
  | some instruction =>
    rw [last] at lowered
    change some (block.statements.foldr
      (fun statement next => .seq (.instruction (.statement statement.kind)) next)
      (.instruction instruction)) = some program at lowered
    simp only [Option.some.injEq] at lowered
    subst program
    rw [← Array.foldr_toList]
    induction block.statements.toList with
    | nil => exact .last _
    | cons s _ ih => exact .statement s.kind ih

/-- A checked block can return to any block entry satisfying the invariant
or leave the function's scope and establish its return postcondition.
This checks every reachable instruction, including prefixes of looping blocks. -/
theorem body_of_blocks {start : State} {depth : Nat} {entry post : State → Prop}
    (inside : depth ≤ start.stack.frames.size) (initial : entry start)
    (blocks : ∀ before, entry before → depth ≤ before.stack.frames.size →
      ∃ (block : BasicBlock) (program : Program hooks allowed), lowerBlock block = some program ∧
        Triple program (· = before)
          (fun _ after => (depth ≤ after.stack.frames.size ∧ entry after) ∨
            (after.stack.frames.size < depth ∧ post after))
          (fun error _ => RunLoop.reportsUB error = false)) :
    FunctionBody.UBFree (Step.step hooks) (fun state => state.stack.frames.size) allowed depth start ∧
    FunctionBody.NormalPost (Step.step hooks) (fun state => state.stack.frames.size) allowed depth
      start post := by
  let boundary := fun after : State =>
    (depth ≤ after.stack.frames.size ∧ entry after) ∨ (after.stack.frames.size < depth ∧ post after)
  let nonUB := fun (error : StepError) (_ : State) => RunLoop.reportsUB error = false
  let invariant := fun state : State => boundary state ∨
    (depth ≤ state.stack.frames.size ∧
      ∃ program : Program hooks allowed, BlockSuffix program ∧ pre program boundary nonUB state)
  have advance (before : State) (active : depth ≤ before.stack.frames.size)
      (valid : invariant before) : stepPre hooks allowed true invariant nonUB before := by
    have suffix : ∃ program : Program hooks allowed, BlockSuffix program ∧ pre program boundary nonUB before := by
      rcases valid with (⟨_, ready⟩ | ⟨outside, _⟩) | ⟨_, pending⟩
      · obtain ⟨block, program, lowered, triple⟩ := blocks before ready active
        exact ⟨program, lowered_suffix lowered, Triple.le_wp triple before rfl⟩
      · exact (Nat.not_lt_of_ge active outside).elim
      · exact pending
    obtain ⟨program, code, verified⟩ := suffix
    cases code with
    | last =>
      exact stepPre_mono (fun _ done => Or.inl done) (fun _ _ safe => safe) before verified.2
    | @statement kind rest tail =>
      refine ⟨verified.2.1, fun choice permitted => ?_⟩
      rcases outcome : Step.step hooks choice before with ⟨after, result⟩
      have checked := stepPre_outcome verified.2 ⟨choice, permitted, outcome⟩
      cases result with
      | error error => simpa only [outcome] using checked
      | ok more =>
        obtain ⟨rfl, pending⟩ := checked
        have same := successful_statement_depth choice verified.1 outcome
        simp only [outcome, true_and]
        exact Or.inr ⟨same.symm ▸ active, rest, tail, pending⟩
  apply FunctionBody.ofInvariant invariant (Or.inl (Or.inl ⟨inside, initial⟩))
  · intro before after choice valid active permitted outcome
    exact (stepPre_outcome (advance before active valid) ⟨choice, permitted, outcome⟩).2
  · intro before after choice error valid active permitted outcome
    exact stepPre_outcome (advance before active valid) ⟨choice, permitted, outcome⟩
  · intro after valid outside
    rcases valid with (⟨active, _⟩ | ⟨_, done⟩) | ⟨active, _⟩
    · exact (Nat.not_lt_of_ge active outside).elim
    · exact done
    · exact (Nat.not_lt_of_ge active outside).elim

/-- A checked two-instruction body ends below its entry stack depth whenever
both instructions succeed. Either can instead leave a classified non-UB error. -/
theorem twoInstructions_body {first second : Instruction} {start : State} {depth : Nat}
    {post : State → Prop} (inside : depth ≤ start.stack.frames.size)
    (firstInScope : ∀ after choice, allowed start choice →
      Step.step hooks choice start = (after, .ok true) → depth ≤ after.stack.frames.size)
    (verified : pre (Program.seq (Program.instruction (hooks := hooks) (allowed := allowed) first)
        (Program.instruction second))
      (fun state => state.stack.frames.size < depth ∧ post state)
      (fun error _ => RunLoop.reportsUB error = false) start) :
    FunctionBody.UBFree (Step.step hooks) (fun state => state.stack.frames.size) allowed depth start ∧
    FunctionBody.NormalPost (Step.step hooks) (fun state => state.stack.frames.size) allowed depth start
      post := by
  let final := fun state : State => state.stack.frames.size < depth ∧ post state
  let onError := fun (error : StepError) (_ : State) => RunLoop.reportsUB error = false
  let pending := fun state => second.matches state ∧ stepPre hooks allowed true final onError state
  let invariant := fun state => state = start ∨
    (depth ≤ state.stack.frames.size ∧ pending state) ∨ final state
  have initially : stepPre hooks allowed true pending onError start := verified.2
  apply FunctionBody.ofInvariant invariant (Or.inl rfl)
  · intro before after choice inv hdepth permitted outcome
    rcases inv with rfl | ⟨_, next⟩ | done
    · have next := (stepPre_outcome initially ⟨choice, permitted, outcome⟩).2
      exact Or.inr (Or.inl ⟨firstInScope after choice permitted outcome, next⟩)
    · exact Or.inr (Or.inr (stepPre_outcome next.2 ⟨choice, permitted, outcome⟩).2)
    · exact False.elim (Nat.not_lt_of_ge hdepth done.1)
  · intro before after choice error inv hdepth permitted outcome
    rcases inv with rfl | ⟨_, next⟩ | done
    · exact stepPre_outcome initially ⟨choice, permitted, outcome⟩
    · exact stepPre_outcome next.2 ⟨choice, permitted, outcome⟩
    · exact False.elim (Nat.not_lt_of_ge hdepth done.1)
  · intro state inv outside
    rcases inv with rfl | ⟨hdepth, _⟩ | done
    · exact False.elim (Nat.not_lt_of_ge inside outside)
    · exact False.elim (Nat.not_lt_of_ge hdepth outside)
    · exact done.2

/-- Observe that the driver has no current frame. -/
def checkEmptyStack (hooks : Hooks) (allowed : State → C → Prop) : Program hooks allowed :=
  .step false

@[spec] theorem spec_checkEmptyStack (hooks : Hooks) (allowed : State → C → Prop)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (checkEmptyStack hooks allowed)
      (fun state => state.stack.currentFrame? = none ∧
        (∃ choice, allowed state choice) ∧ post () state) post onError := by
  apply Triple.iff.mpr
  rintro state ⟨empty, enabled, hpost⟩
  change stepPre hooks allowed false (post ()) onError state
  refine ⟨enabled, ?_⟩
  intro choice _
  change (match Step.step hooks choice state with
    | (after, .ok actual) => actual = false ∧ post () after
    | (after, .error error) => onError error after)
  simpa [Step.step, empty] using hpost

end Miri.Verification.StepWP
