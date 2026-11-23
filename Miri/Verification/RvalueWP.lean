import Miri.Verification.EffectSpecs
import Miri.Verification.InstructionWP
import Lean.Meta.Tactic.Simp.RegisterCommand

/-! Exact preconditions for assignment, following the order of the rvalue
dispatcher and preserving the state at every failed effect. -/
/-- Opt-in simplification rules for a selected MIR rvalue and the production
hooks used by its continuation. -/
register_simp_attr miri_rvalue

namespace Miri.Verification.RvalueWP

open Miri.ABI Miri.Interpreter Miri.MIR Miri.Memory
open Miri.TreeBorrows.RetagPolicy Std.WP

variable {P S C V A B : Type}

/-- Pull back a success and an error continuation through a single effect. -/
def actionPre (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) : Prop :=
  match action before with
  | .ok value after => post value after
  | .error error failed => onError error failed

theorem actionPre_bind (action : RvalueM S A) (next : A → RvalueM S B)
    (post : B → S → Prop) (onError : StepError → S → Prop) (before : S) :
    actionPre (action >>= next) post onError before =
      actionPre action (fun value => actionPre (next value) post onError) onError before := by
  unfold actionPre
  cases result : action before <;> simp [bind, Bind.bind, EStateM.bind, result]

theorem actionPre_ok {action : RvalueM S A} {before after : S} {value : A}
    (ran : action before = .ok value after) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre action post onError before = post value after := by
  simp only [actionPre, ran]

theorem actionPre_pure (value : A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre (pure value) post onError before = post value before := rfl

theorem actionPre_throw (error : StepError) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre (throw error) post onError before = onError error before := rfl

theorem actionPre_run (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    actionPre action post onError before ↔
      InstructionWP.resultPre post onError (runRvalue action before) := by
  unfold actionPre runRvalue
  cases action before <;> rfl

theorem actionPre_bind_fun (action : RvalueM S A) (next : A → RvalueM S B)
    (post : B → S → Prop) (onError : StepError → S → Prop) :
    actionPre (action >>= next) post onError =
      actionPre action (fun value => actionPre (next value) post onError) onError :=
  funext (actionPre_bind action next post onError)

theorem actionPre_ite (guard : Prop) [Decidable guard] (yes no : RvalueM S A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    actionPre (if guard then yes else no) post onError =
      if guard then actionPre yes post onError else actionPre no post onError := by
  by_cases guard <;> simp [*]

private theorem actionPre_congr (action : RvalueM S A) (onError : StepError → S → Prop) (before : S)
    {left right : A → S → Prop} (same : ∀ value state, left value state = right value state) :
    actionPre action left onError before = actionPre action right onError before := by
  rw [show left = right from funext fun value => funext (same value)]

/-- The symbolic pullback is Lean's error-state WP, so registered effect
rules can continue from any remaining rvalue action. -/
theorem actionPre_eq_wp (action : RvalueM S A) (post : A → S → Prop)
    (onError : StepError → S → Prop) :
    actionPre action post onError = wp action post onError := by
  funext before
  simp only [actionPre, wp, WP.wpTrans]
  cases action before <;> rfl

/-- Check the destination first and pull the postcondition through each
operation selected by the rvalue. A retag scope is a higher-order hook, so its
body remains an action until a concrete implementation of the scope is known. -/
def evalPre (hooks : RvalueHooks P S C V) (choice : C)
    (value : Rvalue) (place : Place) (post : S → Prop)
    (onError : StepError → S → Prop) (before : S) : Prop :=
  let pull := fun {A : Type} (action : RvalueM S A) (next : A → S → Prop) =>
    actionPre action next onError
  let finish := fun action => pull (A := Unit) action (fun _ => post)
  (pull (hooks.evalPlace choice place true) fun dest =>
    let layout := hooks.placeLayout dest
    let write := fun (result : RvalueImmTy P) => finish (hooks.writeImmediate choice result.imm dest)
    let writeChecked := fun (result : RvalueImmTy P) =>
      if result.layout == layout then write result
      else onError (.invalidProgram "rvalue result layout mismatch")
    match value with
    | .ThreadLocalRef definition =>
      pull (hooks.threadLocalPointer choice definition) fun pointer =>
        finish (hooks.writePointer choice pointer dest)
    | .Use operand retag =>
      pull (hooks.evalOperand choice operand (some layout)) fun op =>
        finish (hooks.withRetagMode choice (if retag == .Yes then .Default else .None)
          (hooks.copyOp choice op dest))
    | .CopyForDeref _ => onError (.invalidProgram "CopyForDeref in runtime MIR")
    | .BinaryOp operator left right =>
      pull (hooks.evalOperand choice left (if operator.leftHomogeneous then some layout else none)) fun left =>
      pull (hooks.readImmediate choice left) fun left =>
      pull (hooks.evalOperand choice right (if operator.rightHomogeneous then some left.layout else none)) fun right =>
      pull (hooks.readImmediate choice right) fun right =>
      pull (hooks.binaryOp choice operator left right) writeChecked
    | .UnaryOp operator operand =>
      pull (hooks.evalOperand choice operand (if operator.homogeneous then some layout else none)) fun op =>
      pull (hooks.readImmediate choice op) fun operand =>
      pull (hooks.unaryOp choice operator operand) writeChecked
    | .Aggregate kind operands => finish (hooks.writeAggregate choice kind operands dest)
    | .Repeat operand _ => finish (hooks.writeRepeat choice operand dest)
    | .Ref _ borrow src =>
      pull (hooks.evalPlace choice src true) fun src =>
      pull (hooks.forceAllocation choice src) fun memory =>
      pull (hooks.toRef choice memory) fun imm =>
        let val : RvalueImmTy P := ⟨imm, layout⟩
        let mode := if borrow == .Mut .TwoPhaseBorrow then RetagMode.TwoPhase else .Default
        finish (hooks.withRetagMode choice mode do
          let mut val := val
          if !(← hooks.enforceValidity choice val.layout) then
            if let some newVal ← hooks.retagPtrValue choice val val.layout.ty then val := newVal
          hooks.writeImmediate choice val.imm dest)
    | .Reborrow _ mutability src =>
      pull (hooks.evalPlaceToOp choice src none) fun op =>
        if mutability == .Not then finish (hooks.copyOpAllowTransmute choice op dest)
        else finish (hooks.copyOp choice op dest)
    | .RawPtr kind src =>
      pull (hooks.placeBaseRaw choice src) fun baseRaw =>
      pull (hooks.evalPlace choice src false) fun src =>
      pull (hooks.forceAllocation choice src) fun memory =>
      pull (hooks.toRef choice memory) fun imm =>
        let val : RvalueImmTy P := ⟨imm, layout⟩
        if !baseRaw && kind != .FakeForPtrMetadata then
          pull (hooks.withRetagMode choice .Raw do
            return (← hooks.retagPtrValue choice val val.layout.ty).getD val) write
        else write val
    | .Cast kind operand ty =>
      pull (hooks.evalOperand choice operand none) fun src =>
        finish (hooks.cast choice src kind ty dest)
    | .Discriminant src =>
      pull (hooks.evalPlaceToOp choice src none) fun op =>
      pull (hooks.readDiscriminant choice op) fun variant =>
      pull (hooks.discriminantForVariant choice op.layout.ty variant) write
    | .WrapUnsafeBinder operand _ =>
      pull (hooks.evalOperand choice operand none) fun op =>
        finish (hooks.copyOpAllowTransmute choice op dest)) before

theorem evalPre_iff (hooks : RvalueHooks P S C V) (choice : C)
    (value : Rvalue) (place : Place) (post : S → Prop)
    (onError : StepError → S → Prop) (before : S) :
    evalPre hooks choice value place post onError before ↔
      actionPre (evalRvalueIntoPlace hooks choice value place) (fun _ => post) onError before := by
  cases value <;> simp only [evalPre, evalRvalueIntoPlace, actionPre_bind_fun, actionPre_ite]
  all_goals try with_unfolding_all rfl
  all_goals
    apply iff_of_eq
    apply actionPre_congr
    intro dest afterDest
    repeat' (apply actionPre_congr; intro _ _)
    rename_i result state
    change _ = actionPre
      (if result.layout == hooks.placeLayout dest then pure ()
       else throw (.invalidProgram "rvalue result layout mismatch")) _ _ state
    split <;> simp_all only [actionPre_pure, actionPre_throw]

section Canonical

variable {K U O X Host : Type}
local notation "State" => MachineHooks.State K U

private def restoreModePre (old : RetagMode) (post : State → Prop)
    (onError : StepError → State → Prop) (after : State) : Prop :=
  match after.machine.borrowTracker with
  | none => onError (.invalidProgram "borrow tracker removed during retag mode scope") after
  | some tracker => post { after with machine.borrowTracker := some { tracker with retagMode := old } }

/-- Enter the requested Tree Borrows mode and restore the caller's mode in
both continuations. A missing tracker in the resulting state overrides the
body outcome with the interpreter's invariant error. -/
def retagModePre (mode : RetagMode) (action : RvalueM State A) (post : A → State → Prop)
    (onError : StepError → State → Prop) (before : State) : Prop :=
  match before.machine.borrowTracker with
  | none => actionPre action post onError before
  | some tracker =>
    let entered := { before with machine.borrowTracker := some { tracker with retagMode := mode } }
    actionPre action (fun value => restoreModePre tracker.retagMode (post value) onError)
      (fun error => restoreModePre tracker.retagMode (onError error) onError) entered

theorem actionPre_withRetagMode (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) (before : State) :
    actionPre (MachineHooks.withRetagMode mode action) post onError before =
      retagModePre mode action post onError before := by
  cases tracking : before.machine.borrowTracker with
  | none => simp only [retagModePre, actionPre, MachineHooks.withRetagMode, tracking]
  | some tracker =>
    simp only [retagModePre, actionPre, MachineHooks.withRetagMode, tracking]
    let entered : State := { before with machine.borrowTracker := some { tracker with retagMode := mode } }
    generalize action entered = result
    cases result with
    | ok value after => cases restored : after.machine.borrowTracker <;> simp [restoreModePre, restored]
    | error error after => cases restored : after.machine.borrowTracker <;> simp [restoreModePre, restored]

@[spec] theorem spec_withRetagMode (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    Triple (MachineHooks.withRetagMode mode action) (retagModePre mode action post onError)
      post onError :=
  Triple.iff.mpr fun before checked => by
    rw [← actionPre_eq_wp, actionPre_withRetagMode]
    exact checked

@[spec] theorem canonical_withRetagMode [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (mode : RetagMode) (action : RvalueM State A) :
    (ExecutionMachine.rvalueHooks config limits).withRetagMode choice mode action =
      MachineHooks.withRetagMode mode action := rfl

theorem canonical_placeLayout [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).placeLayout dest = dest.layout := rfl

@[spec] theorem canonical_readImmediate [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance) :
    (ExecutionMachine.rvalueHooks config limits).readImmediate choice operand =
      PlaceMachine.readImmediate config.access operand := rfl

@[spec] theorem canonical_writeImmediate [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (value : Immediate Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).writeImmediate choice value dest =
      writePlaceImmediate (ExecutionMachine.projectionHooks config).place choice value dest := rfl

@[spec] theorem canonical_copyOp [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source : OpTy Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).copyOp choice source dest =
      copyRuntimePlace (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy choice source dest false := rfl

@[spec] theorem canonical_copyOpAllowTransmute [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source : OpTy Provenance) (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).copyOpAllowTransmute choice source dest =
      copyRuntimePlace (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy choice source dest true := rfl

@[spec] theorem canonical_memoryCopy [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (source dest : MPlaceTy Provenance) :
    (ExecutionMachine.withValidation config limits).copy.memoryCopy choice source dest =
      GlobalMemoryCopyMachine.typedCopy config.access config.addresses config.arithmetic
        config.projection.dynamic config.projection.dynamicFuel config.compiler.debugAssertions
        choice source dest := rfl

/-- Specialize the retag scope rule without unfolding the other rvalue
hooks of the execution machine. -/
theorem actionPre_rvalueHooks_withRetagMode [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (mode : RetagMode) (action : RvalueM State A)
    (post : A → State → Prop) (onError : StepError → State → Prop) :
    actionPre ((ExecutionMachine.rvalueHooks config limits).withRetagMode choice mode action)
      post onError = retagModePre mode action post onError :=
  funext (actionPre_withRetagMode mode action post onError)

end Canonical

end Miri.Verification.RvalueWP
