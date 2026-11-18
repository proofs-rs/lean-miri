import Miri.Interpreter.ExecutionMachine
import Miri.Verification.StepWP

/-! Equational specs expose the real effectful MIR operations to `vcgen`.
Their callbacks keep the original error and state transitions. -/
namespace Miri.Verification.EffectSpecs

open Miri.Interpreter Miri.MIR
open Miri.ABI Miri.Memory Std.WP

-- Each definition contributes its kernel-checked unfold equation. This keeps
-- constructor matching, error order and flags shared with the interpreter.
attribute [spec] evalRvalueIntoPlace
attribute [spec] OperandMachine.evalOperand OperandMachine.evalPlaceToOp OperandMachine.project
attribute [spec] PlaceDynamic.evalPlace PlaceDynamic.project PlaceDynamic.field PlaceDynamic.downcast
attribute [spec] ScalarOps.binary ScalarOps.unary ExecutionScalar.integerBinary ExecutionScalar.pointerBinary
attribute [spec] Cast.cast Cast.castFromIntLike
attribute [spec] writeAggregate Discriminant.readDiscriminant Discriminant.discriminantForVariant
attribute [spec] Call.evalCallTerminator Call.evalCalleeAndArgs Call.evalFnCallArgument
attribute [spec] Intrinsics.evalNondivergingWith Intrinsics.copyWith
attribute [spec] GlobalMemoryCopyMachine.genericCopy
attribute [spec] MachineHooks.storageLiveDyn MachineHooks.storageDead
attribute [spec] Call.initFnCall Call.initDropInPlaceCall
attribute [spec] PlaceMachine.readImmediate copyRuntimePlace

variable {P L E M C : Type}
local notation "State" => StepState P L E M

/-- The successful effect of a statement must still pass the driver's
post-statement checks. A failure here is checked against the same error postcondition. -/
def afterStatement (oldIndex : Nat) (post : State → Prop)
    (onError : StepError → State → Prop) (after : State) : Prop :=
  match Step.finishStatement oldIndex (after, .ok ()) with
  | (state, .ok more) => more = true ∧ post state
  | (state, .error error) => onError error state

/-- Check a statement's effect in Lean's error-state WP, retaining the actual
post-statement checks and the failed state from either stage. -/
theorem statement_transition_iff (allowed : State → C → Prop)
    (effect : C → EStateM StepError State Unit) (post : State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    StepWP.transitionPre allowed true
      (fun choice => Step.finishStatement (before.stack.frames.size - 1)
        (runRvalue (effect choice) before)) post onError before ↔
    (∃ choice, allowed before choice) ∧
      ∀ choice, allowed before choice →
        wp (effect choice) (fun _ => afterStatement (before.stack.frames.size - 1) post onError)
          onError before := by
  apply and_congr_right
  intro _
  apply forall_congr'
  intro choice
  apply imp_congr_right
  intro _
  simp only [wp, WP.wpTrans]
  cases executed : effect choice before with
  | ok value state => cases value; simp only [runRvalue, executed, afterStatement]; rfl
  | error error state => simp only [runRvalue, executed]; rfl

/-- The production assignment hook uses the same RvalueM action as the
operand, projection and rvalue rules above. -/
theorem assign_transition_iff {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (allowed : MachineHooks.State K U → C → Prop) (dest : Place) (rhs : Rvalue)
    (post : MachineHooks.State K U → Prop) (onError : StepError → MachineHooks.State K U → Prop)
    (before : MachineHooks.State K U) :
    StepWP.transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1)
        ((ExecutionMachine.stepHooks config limits).assign c dest rhs before)) post onError before ↔
    (∃ choice, allowed before choice) ∧
      ∀ choice, allowed before choice →
        wp (evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
          (ExecutionMachine.withValidation config limits) limits) choice rhs dest)
          (fun _ => afterStatement (before.stack.frames.size - 1) post onError) onError before := by
  exact statement_transition_iff allowed (fun choice =>
      evalRvalueIntoPlace (ExecutionMachine.rvalueHooks
        (ExecutionMachine.withValidation config limits) limits) choice rhs dest) post onError before

/-- Lift an exact interpreter result to an error-state effect. -/
def toEffect {S A : Type} (run : S → StepResult S A) : EStateM StepError S A :=
  fun state => match run state with
    | (after, .ok value) => .ok value after
    | (after, .error error) => .error error after

/-- Keep the result and the resulting state as proof obligations at the
boundary of an interpreter callback. -/
@[spec low] theorem spec_toEffect {S A : Type} (run : S → StepResult S A)
    (post : A → S → Prop) (onError : StepError → S → Prop) :
    Triple (toEffect run)
      (fun state => match run state with
        | (after, .ok value) => post value after
        | (after, .error error) => onError error after)
      post onError := by
  apply Triple.iff.mpr
  intro state safe
  simp only [wp, WP.wpTrans]
  rcases outcome : run state with ⟨after, result⟩
  cases result <;> simpa only [toEffect, outcome] using safe

@[spec] theorem machine_run_effect {K U A : Type} (action : MachineHooks.M K U A) :
    toEffect (MachineHooks.run action) = action := by
  funext state
  cases ran : action state <;> simp [toEffect, MachineHooks.run, Call.run, ran]

@[spec high] theorem toEffect_discard {S A : Type} (run : S → StepResult S A) :
    toEffect (fun state =>
      let result := run state
      (result.1, result.2.map fun _ => ())) =
      (do let _ ← toEffect run; pure ()) := by
  funext state
  rcases ran : run state with ⟨after, result⟩
  cases result <;>
    simp [toEffect, Except.map, ran, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem statement_callback_iff (allowed : State → C → Prop)
    (effect : C → State → StepResult State Unit) (post : State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    StepWP.transitionPre allowed true
      (fun choice => Step.finishStatement (before.stack.frames.size - 1) (effect choice before))
      post onError before ↔
    (∃ choice, allowed before choice) ∧
      ∀ choice, allowed before choice →
        wp (toEffect (effect choice)) (fun _ => afterStatement (before.stack.frames.size - 1) post onError)
          onError before := by
  have same : (fun choice => runRvalue (toEffect (effect choice)) before) =
      fun choice => effect choice before := by
    funext choice
    rcases result : effect choice before with ⟨after, outcome⟩
    cases outcome <;> simp [runRvalue, toEffect, result]
  have rule := statement_transition_iff allowed (fun choice => toEffect (effect choice))
    post onError before
  have completed := congrArg (fun run choice => Step.finishStatement (before.stack.frames.size - 1)
    (run choice)) same
  rw [completed] at rule
  exact rule

/-- Preserve the callback order and the original selected terminator across
the pre-terminator action. -/
def terminatorEffect {V : Type} (hooks : StepHooks P L E M C V)
    (choice : C) (term : Terminator) : EStateM StepError State Unit := do
  toEffect (hooks.beforeTerminator choice)
  toEffect (hooks.terminator choice term)

attribute [spec] terminatorEffect

theorem terminator_transition_iff {V : Type} (hooks : StepHooks P L E M C V)
    (allowed : State → C → Prop) (term : Terminator) (post : State → Prop)
    (onError : StepError → State → Prop) (before : State) :
    StepWP.transitionPre allowed true (fun choice => Step.runTerminator hooks choice term before)
      post onError before ↔
      (∃ choice, allowed before choice) ∧ ∀ choice, allowed before choice →
        wp (terminatorEffect hooks choice term) (fun _ => post) onError before := by
  apply and_congr_right
  intro _
  apply forall_congr'
  intro choice
  apply imp_congr_right
  intro _
  simp only [wp, WP.wpTrans, terminatorEffect, bind, Bind.bind, EStateM.bind, toEffect]
  rcases started : hooks.beforeTerminator choice before with ⟨state, result⟩
  cases result with
  | error error => simp [Step.runTerminator, started]
  | ok value =>
    cases value
    rcases evaluated : hooks.terminator choice term state with ⟨after, result⟩
    cases result with
    | error error => simp [Step.runTerminator, started, evaluated] <;> rfl
    | ok value =>
      simp [Step.runTerminator, started, evaluated]
      change (true = true ∧ post after) ↔ post after
      simp

variable {Op Imm : Type}
local notation "TermHooks" => TerminatorHooks P L E M C Op Imm

/-- Decompose a switch into discriminant evaluation, ordered comparison and
the actual jump. The comparison action carries its own error state. -/
@[spec high] theorem switch_effect (hooks : TermHooks) (choice : C)
    (discr : Operand) (targets : SwitchTargets) :
    toEffect (ControlFlow.evalSwitchInt hooks choice discr targets) =
      (do
        let value ← toEffect (hooks.evalDiscriminant choice discr)
        let target ← toEffect (ControlFlow.selectSwitchTarget hooks choice value targets)
        toEffect (ControlFlow.goToBlock target)) := by
  funext before
  rcases start : hooks.evalDiscriminant choice discr before with ⟨state, result⟩
  cases result with
  | error error => simp [ControlFlow.evalSwitchInt, toEffect, bind, Bind.bind, EStateM.bind, start]
  | ok value =>
    rcases selected : ControlFlow.selectSwitchTarget hooks choice value targets state with ⟨after, result⟩
    cases result <;> simp [ControlFlow.evalSwitchInt, toEffect, bind, Bind.bind, EStateM.bind, Id.run, pure, Pure.pure, start, selected] <;> rfl

@[spec high] theorem assert_effect (hooks : TermHooks) (choice : C)
    (condition : Operand) (expected : Bool) (message : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction) :
    toEffect (ControlFlow.evalAssert hooks choice condition expected message target unwind) =
      (do
        let before ← get
        let ignored := hooks.ignoreOptionalOverflowChecks before && ControlFlow.isOptionalOverflowCheck message
        let actual ← toEffect (hooks.readAssertCondition choice condition)
        if ignored || expected == actual then toEffect (ControlFlow.goToBlock target)
        else toEffect (hooks.assertPanic choice message unwind)) := by
  funext before
  rcases read : hooks.readAssertCondition choice condition before with ⟨state, result⟩
  cases result with
  | error error =>
    simp [ControlFlow.evalAssert, toEffect, bind, Bind.bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, read]
  | ok actual =>
    by_cases pass : (hooks.ignoreOptionalOverflowChecks before &&
        ControlFlow.isOptionalOverflowCheck message || expected == actual) = true
    <;> simp only [ControlFlow.evalAssert, toEffect, bind, Bind.bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, read, pass, ite_eq_left, Id.run, pure, Pure.pure] <;> rfl

@[spec high] theorem call_effect (hooks : TermHooks) (choice : C)
    (term : Terminator) (target : Option BasicBlockId) :
    toEffect (ControlFlow.evalCall hooks choice term target) =
      (do
        let before ← get
        toEffect (hooks.call choice term)
        let after ← get
        if target.isSome && after.stack.frames.size == before.stack.frames.size &&
            after.stack.currentFrame?.map (·.location) == before.stack.currentFrame?.map (·.location) then
          throw (.invalidProgram "evaluating this call made no progress")) := by
  funext before
  rcases called : hooks.call choice term before with ⟨after, result⟩
  cases result with
  | error error =>
    simp [ControlFlow.evalCall, toEffect, bind, Bind.bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, called]
  | ok value =>
    cases value
    by_cases stalled : (target.isSome && after.stack.frames.size == before.stack.frames.size &&
        after.stack.currentFrame?.map (·.location) == before.stack.currentFrame?.map (·.location)) = true
    <;> simp only [ControlFlow.evalCall, toEffect, bind, Bind.bind, EStateM.bind, pure, Pure.pure, Id.run,
      throw, get, getThe, MonadStateOf.get,
      EStateM.get, called, stalled, ite_eq_left] <;> rfl

@[spec high] theorem drop_effect (hooks : TermHooks) (choice : C)
    (place : Place) (target : BasicBlockId) (unwind : UnwindAction) (asyncDrop : Option BasicBlockId) :
    toEffect (ControlFlow.evalDrop hooks choice place target unwind asyncDrop) =
      (if asyncDrop.isSome then throw (.invalidProgram "Async Drop must be expanded or reset to sync")
       else toEffect (hooks.drop choice place target unwind)) := by
  cases asyncDrop <;> rfl

/-- Turn the canonical selected-terminator callback into its actual
effect, so registered terminator rules can be used after the pre-hook. -/
@[spec high] theorem canonical_terminator_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (term : Terminator) :
    toEffect ((ExecutionMachine.stepHooks config limits).terminator choice term) =
      toEffect (ControlFlow.evalTerminator (ExecutionMachine.terminatorHooks config limits) choice term) :=
  rfl

@[spec high] theorem switch_dispatch (hooks : TermHooks) (choice : C) (info : SourceInfo)
    (discr : Operand) (targets : SwitchTargets) :
    toEffect (ControlFlow.evalTerminator hooks choice ⟨info, .SwitchInt discr targets⟩) =
      toEffect (ControlFlow.evalSwitchInt hooks choice discr targets) := rfl

@[spec high] theorem assert_dispatch (hooks : TermHooks) (choice : C) (info : SourceInfo)
    (condition : Operand) (expected : Bool) (message : AssertKind)
    (target : BasicBlockId) (unwind : UnwindAction) :
    toEffect (ControlFlow.evalTerminator hooks choice ⟨info, .Assert condition expected message target unwind⟩) =
      toEffect (ControlFlow.evalAssert hooks choice condition expected message target unwind) := rfl

@[spec high] theorem call_dispatch (hooks : TermHooks) (choice : C) (info : SourceInfo)
    (callee : Operand) (args : Array SpannedOperand) (place : Place)
    (target : Option BasicBlockId) (unwind : UnwindAction) (source : CallSource) (span : SpanRef) :
    toEffect (ControlFlow.evalTerminator hooks choice ⟨info, .Call callee args place target unwind source span⟩) =
      toEffect (ControlFlow.evalCall hooks choice ⟨info, .Call callee args place target unwind source span⟩ target) := rfl

@[spec high] theorem drop_dispatch (hooks : TermHooks) (choice : C) (info : SourceInfo)
    (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
    (replace : Bool) (asyncDrop : Option BasicBlockId) :
    toEffect (ControlFlow.evalTerminator hooks choice ⟨info, .Drop place target unwind replace asyncDrop⟩) =
      toEffect (ControlFlow.evalDrop hooks choice place target unwind asyncDrop) := rfl

@[spec high] theorem canonical_call_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (term : Terminator) :
    toEffect ((ExecutionMachine.terminatorHooks config limits).call choice term) =
      Call.evalCallTerminator (ExecutionMachine.callHooks
        (ExecutionMachine.withValidation config limits) limits) choice limits.callDispatch term :=
  machine_run_effect _

@[spec high] theorem canonical_drop_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (target : BasicBlockId) (unwind : UnwindAction) :
    toEffect ((ExecutionMachine.terminatorHooks config limits).drop choice place target unwind) =
      (do
        let config := ExecutionMachine.withValidation config limits
        let calls := ExecutionMachine.callHooks config limits
        let dest ← PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks config) choice place false
        let callee ← calls.resolveDropGlue choice dest.layout.ty
        match ← calls.instanceKind callee with
        | .Shim (.DropGlue _ none) =>
          let state ← get
          let (state, outcome) := ControlFlow.goToBlock target state
          set state
          match outcome with
          | .ok value => pure value
          | .error error => throw error
        | _ => Call.initDropInPlaceCall calls choice limits.callDispatch dest.stackView callee target unwind) := by
  change toEffect (MachineHooks.run _) = _
  rw [machine_run_effect]
  dsimp only
  congr 1
  funext dest
  congr 1
  funext callee
  congr 1
  funext instanceKind
  cases instanceKind <;> try rfl
  rename_i shim
  cases shim <;> try rfl
  rename_i entry
  cases entry <;> try rfl
  dsimp only
  congr 1
  funext state
  congr 1
  cases (ControlFlow.goToBlock target state).2 <;> rfl

@[spec high] theorem canonical_intrinsic_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (intrinsic : NonDivergingIntrinsic) :
    toEffect ((ExecutionMachine.stepHooks config limits).intrinsic choice intrinsic) =
      Intrinsics.evalNondivergingWith
        (ExecutionMachine.memoryIntrinsicHooks (ExecutionMachine.withValidation config limits))
        (fun c op => OperandMachine.evalOperand
          (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) c op none)
        choice intrinsic :=
  machine_run_effect _

@[spec] theorem canonical_intrinsic_copy {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host)
    (choice : C) (source dest : Pointer (Option Provenance)) (size : Size) (nonoverlap : Bool) :
    (ExecutionMachine.memoryIntrinsicHooks config).memCopy choice source dest size nonoverlap =
      GlobalMemoryCopyMachine.genericCopy config.access config.addresses config.arithmetic
        source dest size 1 nonoverlap := rfl

@[spec high] theorem canonical_storageLive_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (localId : LocalId) :
    toEffect ((ExecutionMachine.stepHooks config limits).storageLive choice localId) =
      MachineHooks.storageLiveDyn (ExecutionMachine.withValidation config limits).lifecycle.storage
        localId .none :=
  machine_run_effect _

@[spec high] theorem canonical_storageDead_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (localId : LocalId) :
    toEffect ((ExecutionMachine.stepHooks config limits).storageDead choice localId) =
      MachineHooks.storageDead (ExecutionMachine.withValidation config limits).lifecycle.storage localId :=
  machine_run_effect _

@[spec high] theorem canonical_place_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (skipValidity : Bool) :
    toEffect ((ExecutionMachine.stepHooks config limits).evalPlace choice place skipValidity) =
      PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
        choice place skipValidity :=
  machine_run_effect _

@[spec high] theorem canonical_discriminant_effect {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : Operand) :
    toEffect ((ExecutionMachine.terminatorHooks config limits).evalDiscriminant choice operand) =
      (do
        let config := ExecutionMachine.withValidation config limits
        let value ← OperandMachine.evalOperand (ExecutionMachine.operandHooks config) choice operand none
        PlaceMachine.readImmediate config.access value) :=
  machine_run_effect _

-- Reduce projections of the production rvalue hooks without expanding the
-- surrounding configuration or repeating the source's evaluation logic.
@[spec] theorem canonical_rvalue_operand {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : Operand) (known : Option LocalLayout) :
    (ExecutionMachine.rvalueHooks config limits).evalOperand choice operand known =
      OperandMachine.evalOperand
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
        choice operand known := rfl

@[spec] theorem canonical_rvalue_place {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (skipValidity : Bool) :
    (ExecutionMachine.rvalueHooks config limits).evalPlace choice place skipValidity =
      PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
        choice place skipValidity := rfl

@[spec] theorem canonical_rvalue_placeToOp {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (place : Place) (known : Option LocalLayout) :
    (ExecutionMachine.rvalueHooks config limits).evalPlaceToOp choice place known =
      OperandMachine.evalPlaceToOp
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
        choice place known := rfl

@[spec] theorem canonical_rvalue_readDiscriminant {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance) :
    (ExecutionMachine.rvalueHooks config limits).readDiscriminant choice operand =
      Discriminant.readDiscriminant
        (ExecutionMachine.discriminantHooks (ExecutionMachine.withValidation config limits))
        choice operand := rfl

@[spec] theorem canonical_rvalue_discriminantForVariant {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (ty : TyId) (variant : VariantIndex) :
    (ExecutionMachine.rvalueHooks config limits).discriminantForVariant choice ty variant =
      Discriminant.discriminantForVariant
        (ExecutionMachine.discriminantHooks (ExecutionMachine.withValidation config limits))
        choice ty variant := rfl

@[spec] theorem canonical_rvalue_binary {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operator : BinOp) (left right : RvalueImmTy Provenance) :
    (ExecutionMachine.rvalueHooks config limits).binaryOp choice operator left right =
      ScalarOps.binary (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
        choice operator left right := rfl

@[spec] theorem canonical_rvalue_unary {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operator : UnOp) (value : RvalueImmTy Provenance) :
    (ExecutionMachine.rvalueHooks config limits).unaryOp choice operator value =
      ScalarOps.unary (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
        choice operator value := rfl

@[spec] theorem canonical_rvalue_cast {K U O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (choice : C) (operand : OpTy Provenance) (kind : CastKind) (ty : TyId)
    (dest : RuntimePlace Provenance) :
    (ExecutionMachine.rvalueHooks config limits).cast choice operand kind ty dest =
      Cast.cast (ExecutionMachine.castHooks (ExecutionMachine.withValidation config limits) limits)
        choice limits.casts operand kind ty dest := rfl

end Miri.Verification.EffectSpecs
