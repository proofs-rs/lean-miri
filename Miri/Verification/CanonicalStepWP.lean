import Miri.Verification.StepWP
import Miri.Interpreter.ExecutionMachine
import Miri.Verification.RvalueWP
import Miri.Verification.ProtectorReleaseWP

/-! Specialize the driver continuations to the assembled execution machine. -/
namespace Miri.Verification.CanonicalStepWP

open Miri.Interpreter Miri.MIR Miri.Verification.StepWP Std.WP

variable {K U C O X Host : Type} [DecidableEq K]
local notation "Config" => ExecutionMachine.Config K U C O X Host
local notation "Limits" => ExecutionMachine.Limits
local notation "State" => MachineHooks.State K U
local notation "Success" => Bool → State → Prop
local notation "Errors" => StepError → State → Prop

/-- The local becomes dead before its stack allocation is deallocated.
A failed deallocation therefore sees the updated frame. -/
def storageDeadPre (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (post : State → Prop) (onError : Errors) (before : State) : Prop :=
  if id == 0 then onError (.stack .cannotMakeReturnPlaceDead) before
  else
    match before.stack.currentFrame? with
    | none => onError (.stack .emptyStack) before
    | some frame =>
      match frame.getLocal id with
      | .error error => onError (.stack error) before
      | .ok old =>
        match frame.replaceLocalValue id .dead with
        | .error error => onError (.stack error) before
        | .ok updated =>
          if before.stack.frames.isEmpty then onError (.stack .emptyStack) before
          else
            let after := { before with stack := ⟨before.stack.frames.pop.push updated⟩ }
            match old.value with
            | .live (.indirect place) =>
              wp (hooks.deallocateStack place.ptr) (fun _ => post) onError after
            | _ => post after

omit [DecidableEq K] in
theorem storageDeadPre_iff (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (post : State → Prop) (onError : Errors) (before : State) :
    storageDeadPre hooks id post onError before ↔
      wp (MachineHooks.storageDead hooks id) (fun _ => post) onError before := by
  simp only [storageDeadPre, MachineHooks.storageDead, wp, WP.wpTrans]
  split
  · rfl
  · simp only [bind, Bind.bind, EStateM.bind, MachineHooks.currentFrame, get, getThe,
      MonadStateOf.get, EStateM.get]
    cases before.stack.currentFrame? with
    | none => rfl
    | some frame =>
      simp only [pure, Pure.pure, EStateM.pure]
      cases frame.getLocal id with
      | error => rfl
      | ok old =>
        simp only [MachineHooks.storageResult_ok, pure, Pure.pure, EStateM.pure]
        cases frame.replaceLocalValue id .dead with
        | error => rfl
        | ok updated =>
          simp only [MachineHooks.storageResult_ok, MachineHooks.setCurrentFrame, bind, Bind.bind,
            EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure]
          by_cases empty : before.stack.frames.isEmpty = true
          · simp only [empty, ite_true]; rfl
          · simp only [empty, Bool.false_eq_true, ↓reduceIte]
            cases oldValue : old.value with
            | dead => rfl
            | live value =>
              cases value <;> rfl

omit [DecidableEq K] in
@[spec high] theorem spec_storageDeadEffect (hooks : MachineHooks.StorageHooks K U) (id : LocalId)
    (post : Unit → State → Prop) (onError : Errors) :
    Triple (MachineHooks.storageDead hooks id)
      (storageDeadPre hooks id (post ()) onError) post onError := by
  apply Triple.iff.mpr
  intro before checked
  have h := (storageDeadPre_iff hooks id (post ()) onError before).mp checked
  simp only [wp, WP.wpTrans] at h ⊢
  cases done : MachineHooks.storageDead hooks id before with
  | error => simpa only [done] using h
  | ok value => cases value; simpa only [done] using h

/-- Unfold statement effects to their canonical machine actions. Assignment
uses its rvalue continuation and effectful statements share the driver's
post-statement check. -/
def statementPre (config : Config) (limits : Limits) (choice : C)
    (kind : StatementKind) (post : Success) (onError : Errors) (before : State) : Prop :=
  let checked := ExecutionMachine.withValidation config limits
  let finish := InstructionWP.finishStatementResultPre (before.stack.frames.size - 1) post onError
  let place (mirPlace : Place) :=
    PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks checked) choice mirPlace false
  match kind with
  | .Assign destination value =>
    RvalueWP.evalPre (ExecutionMachine.rvalueHooks checked limits) choice value destination
      finish onError before
  | .SetDiscriminant mirPlace variant =>
    wp (place mirPlace) (fun dest =>
      wp (Discriminant.writeDiscriminant (ExecutionMachine.discriminantHooks checked)
        choice variant dest) (fun _ => finish) onError) onError before
  | .StorageLive id =>
    wp (MachineHooks.storageLiveDyn checked.lifecycle.storage id .none) (fun _ => finish) onError before
  | .StorageDead id =>
    storageDeadPre checked.lifecycle.storage id finish onError before
  | .Intrinsic intrinsic =>
    wp (Intrinsics.evalNondivergingWith (ExecutionMachine.memoryIntrinsicHooks checked)
      (fun c op => OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) c op none)
      choice intrinsic) (fun _ => finish) onError before
  | .PlaceMention mirPlace => wp (place mirPlace) (fun _ => finish) onError before
  | .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop | .ConstEvalCounter
  | .BackwardIncompatibleDropHint .. => finish before

omit [DecidableEq K] in
private theorem effectWP_iff {A : Type} (action : MachineHooks.M K U A)
    (post : A → State → Prop) (onError : Errors) (before : State) :
    wp action post onError before ↔
      InstructionWP.resultPre post onError (MachineHooks.run action before) := by
  simp only [wp, WP.wpTrans, MachineHooks.run, Call.run]
  cases outcome : action before <;> rfl

theorem statementPre_iff (config : Config) (limits : Limits) (choice : C)
    (kind : StatementKind) (post : Success) (onError : Errors) (before : State) :
    statementPre config limits choice kind post onError before ↔
      StepWP.statementStepPre (ExecutionMachine.stepHooks config limits) choice kind post onError before := by
  cases kind <;> try rfl
  case Assign destination value =>
    simp only [statementPre, RvalueWP.evalPre_iff, StepWP.statementStepPre, InstructionWP.statementPre,
      ExecutionMachine.stepHooks_assign]
    unfold RvalueWP.actionPre MachineHooks.run Call.run
    generalize evalRvalueIntoPlace _ choice value destination = action
    cases action before <;> rfl
  case SetDiscriminant mirPlace variant =>
    simp only [statementPre, StepWP.statementStepPre, InstructionWP.statementPre, effectWP_iff]
    let checked := ExecutionMachine.withValidation config limits
    rcases evaluated : MachineHooks.run
        (PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks checked) choice mirPlace false) before
      with ⟨after, result⟩
    have evaluated' : (ExecutionMachine.stepHooks config limits).evalPlace choice mirPlace false before =
        (after, result) := evaluated
    rw [evaluated']
    cases result with
    | error => rfl
    | ok => exact effectWP_iff _ _ _ _
  case StorageDead =>
    rw [statementPre, storageDeadPre_iff]
    exact effectWP_iff _ _ _ _
  all_goals
    exact effectWP_iff _ _ _ _

attribute [spec] Discriminant.writeDiscriminant Discriminant.tagForVariant

local notation "MachineFrame" =>
  Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra

private def cleanupPointersPre (storage : MachineHooks.StorageHooks K U)
    (post : State → Prop) (onError : Errors) :
    List (Miri.Memory.Pointer (Option Miri.Memory.Provenance)) → State → Prop
  | [], state => post state
  | pointer :: rest, state =>
    RvalueWP.actionPre (storage.deallocateStack pointer)
      (fun _ => cleanupPointersPre storage post onError rest) onError state

private def cleanupLocalsPre (storage : MachineHooks.StorageHooks K U)
    (post : State → Prop) (onError : Errors) :
    List (LocalState Miri.Memory.Provenance LocalLayout) → State → Prop
  | [], state => post state
  | slot :: rest, state =>
    let next := cleanupLocalsPre storage post onError rest
    match slot.value with
    | .live (.indirect place) =>
      RvalueWP.actionPre (storage.deallocateStack place.ptr) (fun _ => next) onError state
    | _ => next state

omit [DecidableEq K] in
private theorem cleanupPointersPre_iff (storage : MachineHooks.StorageHooks K U)
    (post : State → Prop) (onError : Errors) (args : List (MemoryOperandPlace Miri.Memory.Provenance))
    (state : State) :
    cleanupPointersPre storage post onError (args.map (·.mplace.ptr)) state ↔
      RvalueWP.actionPre
        (forIn args () (fun arg _ => do
          storage.deallocateStack arg.mplace.ptr
          pure (.yield ()))) (fun _ => post) onError state := by
  induction args generalizing state with
  | nil => simp [cleanupPointersPre, RvalueWP.actionPre_pure]
  | cons arg rest ih =>
    simp only [List.map_cons, cleanupPointersPre, List.forIn_cons, RvalueWP.actionPre_bind]
    unfold RvalueWP.actionPre
    cases done : storage.deallocateStack arg.mplace.ptr state with
    | error => rfl
    | ok value ready =>
      cases value
      exact ih ready

omit [DecidableEq K] in
private theorem cleanupLocalsPre_iff (storage : MachineHooks.StorageHooks K U)
    (post : State → Prop) (onError : Errors)
    (slots : List (LocalState Miri.Memory.Provenance LocalLayout)) (state : State) :
    cleanupLocalsPre storage post onError slots state ↔
      RvalueWP.actionPre
        (forIn slots () (fun slot _ => do
          if let .live (.indirect place) := slot.value then storage.deallocateStack place.ptr
          pure (.yield ()))) (fun _ => post) onError state := by
  induction slots generalizing state with
  | nil => simp [cleanupLocalsPre, RvalueWP.actionPre_pure]
  | cons slot rest ih =>
    simp only [cleanupLocalsPre, List.forIn_cons, RvalueWP.actionPre_bind]
    cases used : slot.value with
    | dead =>
      simpa only [used, RvalueWP.actionPre_pure] using ih state
    | live value =>
      cases value with
      | immediate =>
        simpa only [used, RvalueWP.actionPre_pure] using ih state
      | indirect place =>
        simp only [RvalueWP.actionPre_bind]
        unfold RvalueWP.actionPre
        cases done : storage.deallocateStack place.ptr state with
        | error => rfl
        | ok value ready =>
          cases value
          exact ih ready

/-- A detached frame's owned locals and varargs are deallocated in order.
The after-pop hook runs after all deallocations succeed. -/
def cleanupFramePre (lifecycle : CallMachine.Lifecycle K U C) (choice : C) (unwinding : Bool)
    (frame : MachineFrame) (post : ReturnAction → State → Prop) (onError : Errors)
    (state : State) : Prop :=
  let cleanup := match frame.returnContinuation with
    | .goto .. => true
    | .stop cleanup => cleanup
  if !cleanup then post .noCleanup state
  else cleanupLocalsPre lifecycle.storage
    (cleanupPointersPre lifecycle.storage
      (RvalueWP.actionPre (lifecycle.afterPop choice frame unwinding) (fun action ready =>
        if action == .noCleanup then
          onError (.invalidProgram "after_stack_pop returned NoCleanup during cleanup") ready
        else post action ready) onError)
      onError (frame.vaList.toList.map (·.mplace.ptr)))
    onError frame.locals.toList state

omit [DecidableEq K] in
theorem cleanupFramePre_iff (lifecycle : CallMachine.Lifecycle K U C) (choice : C)
    (unwinding : Bool) (frame : MachineFrame) (post : ReturnAction → State → Prop) (onError : Errors)
    (state : State) :
    cleanupFramePre lifecycle choice unwinding frame post onError state ↔
      RvalueWP.actionPre (CallMachine.cleanup lifecycle choice unwinding frame) post onError state := by
  unfold cleanupFramePre CallMachine.cleanup
  dsimp only
  cases continuation : frame.returnContinuation
  case' stop cleanup => cases cleanup
  all_goals
    simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      RvalueWP.actionPre_pure, ← Array.forIn_toList, RvalueWP.actionPre_bind_fun]
    try rfl
  all_goals
    rw [cleanupLocalsPre_iff]
    apply iff_of_eq
    congr 1
    funext value after
    apply propext
    rw [cleanupPointersPre_iff]
    apply iff_of_eq
    congr 1
    funext value ready
    unfold RvalueWP.actionPre
    cases lifecycle.afterPop choice frame unwinding ready with
    | error => rfl
    | ok action next =>
      by_cases rejected : (action == .noCleanup) = true <;>
        simp [rejected, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure] <;> rfl

omit [DecidableEq K] in
@[spec high] theorem spec_cleanupFrame (lifecycle : CallMachine.Lifecycle K U C) (choice : C)
    (unwinding : Bool) (frame : MachineFrame) (post : ReturnAction → State → Prop) (onError : Errors) :
    Triple (CallMachine.cleanup lifecycle choice unwinding frame)
      (cleanupFramePre lifecycle choice unwinding frame post onError) post onError := by
  apply Triple.iff.mpr
  intro before checked
  rw [← RvalueWP.actionPre_eq_wp]
  exact (cleanupFramePre_iff lifecycle choice unwinding frame post onError before).mp checked

/-- Return cleanup uses the exact protector-release precondition before the
frame is removed and before its return value is copied. -/
def returnPre (config : Config) (limits : Limits) (choice : C) (unwinding : Bool)
    (post : State → Prop) (onError : Errors) (before : State) : Prop :=
  let validated := ExecutionMachine.withValidation config limits
  let retag := TypedMachineBindings.retagHooks validated.access validated.retag
  InstructionWP.returnPreWithEffects (ExecutionMachine.terminatorHooks config limits).toControlHooks
    choice unwinding (ProtectorReleaseWP.popRawPre retag)
    (cleanupFramePre validated.lifecycle choice unwinding) post onError before

theorem returnPre_iff (config : Config) (limits : Limits) (choice : C) (unwinding : Bool)
    (post : State → Prop) (onError : Errors) (before : State) :
    returnPre config limits choice unwinding post onError before ↔
      InstructionWP.returnPre (ExecutionMachine.terminatorHooks config limits).toControlHooks
        choice unwinding post onError before := by
  unfold returnPre InstructionWP.returnPre
  apply InstructionWP.returnPreWithEffects_congr
  · intro finish failure ready
    rw [ProtectorReleaseWP.popRawPre_iff]
    exact RvalueWP.actionPre_run _ _ _ _
  · intro frame finish failure ready
    rw [cleanupFramePre_iff]
    exact RvalueWP.actionPre_run _ _ _ _

omit [DecidableEq K] in
private theorem callbackWP_iff {A : Type} (run : State → StepResult State A)
    (post : A → State → Prop) (onError : Errors) (before : State) :
    wp (EffectSpecs.toEffect run) post onError before ↔
      InstructionWP.resultPre post onError (run before) := by
  simp only [wp, WP.wpTrans, EffectSpecs.toEffect]
  rcases ran : run before with ⟨after, outcome⟩
  cases outcome <;> rfl

private def assertLift {A : Type} (result : Except StepError A) : MachineHooks.M K U A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

@[spec] theorem canonical_callOperand (config : Config) (limits : Limits) (choice : C)
    (operand : Miri.MIR.Operand) :
    (ExecutionMachine.callHooks config limits).evalOperand choice operand =
      OperandMachine.evalOperand
        (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) choice operand none :=
  rfl

@[spec] theorem canonical_callPlace (config : Config) (limits : Limits) (choice : C)
    (place : Place) (skipValidity : Bool) :
    (ExecutionMachine.callHooks config limits).evalPlace choice place skipValidity =
      (do return (← PlaceDynamic.evalPlace
        (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
        choice place skipValidity).stackView) :=
  rfl

@[spec] theorem canonical_callPlaceToOp (config : Config) (limits : Limits) (choice : C)
    (place : RuntimeStackPlace Miri.Memory.Provenance) :
    (ExecutionMachine.callHooks config limits).placeToOp choice place =
      placeToOp (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
        choice place.toRuntimePlace :=
  rfl

@[spec] theorem canonical_callForceAllocation (config : Config) (limits : Limits) (choice : C)
    (place : RuntimeStackPlace Miri.Memory.Provenance) :
    (ExecutionMachine.callHooks config limits).forceAllocation choice place =
      forceAllocation (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
        choice place.toRuntimePlace :=
  rfl

@[spec] theorem canonical_callCopyArgument (config : Config) (limits : Limits) (choice : C)
    (source : OpTy Miri.Memory.Provenance) (dest : RuntimeStackPlace Miri.Memory.Provenance) :
    (ExecutionMachine.callHooks config limits).copyAllowTransmute choice source dest =
      (let checked := ExecutionMachine.withValidation config limits
       copyRuntimePlace (ExecutionMachine.projectionHooks checked).place checked.copy
         choice source dest.toRuntimePlace true) :=
  rfl

@[spec] theorem canonical_callProtectArgument (config : Config) (limits : Limits) (choice : C)
    (place : MPlaceTy Miri.Memory.Provenance) :
    (ExecutionMachine.callHooks config limits).protectArgument choice place =
      TypedRetag.protectInPlaceFunctionArgument (ExecutionMachine.withValidation config limits).retag
        limits.retag place :=
  rfl

/-- Evaluate and read a MIR assertion operand, preserving each failed effect. -/
def assertConditionEffect (config : Config) (limits : Limits) (choice : C)
    (condition : Miri.MIR.Operand) : MachineHooks.M K U Bool := do
  let checked := ExecutionMachine.withValidation config limits
  let read := do
    let operand ← OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) choice condition none
    PlaceMachine.readImmediate checked.access operand
  let value ← read
  let scalar ← assertLift (value.imm.toScalar.mapError ScalarOps.immediateError)
  assertLift (scalar.toBool.mapError ScalarOps.scalarError)

@[spec] theorem canonical_assertCondition (config : Config) (limits : Limits)
    (choice : C) (condition : Miri.MIR.Operand) :
    EffectSpecs.toEffect ((ExecutionMachine.terminatorHooks config limits).readAssertCondition choice condition) =
      assertConditionEffect config limits choice condition :=
  EffectSpecs.machine_run_effect _

/-- Call the appropriate panic lang item with the original unwind action. -/
def assertPanicEffect (config : Config) (limits : Limits) (choice : C)
    (message : AssertKind) (unwind : UnwindAction) : MachineHooks.M K U Unit :=
  let checked := ExecutionMachine.withValidation config limits
  let call := ExecutionMachine.callHooks checked limits
  let panic := { checked.panic with
    evalOperand := fun c op => OperandMachine.evalOperand (ExecutionMachine.operandHooks checked) c op none
    driver := FunctionCalls.bindUnwind checked.panic.driver (ExecutionCalls.helpers checked.helpers call) }
  Panic.assertPanic panic choice message unwind

@[spec] theorem canonical_assertPanic (config : Config) (limits : Limits) (choice : C)
    (message : AssertKind) (unwind : UnwindAction) :
    EffectSpecs.toEffect ((ExecutionMachine.terminatorHooks config limits).assertPanic choice message unwind) =
      assertPanicEffect config limits choice message unwind :=
  EffectSpecs.machine_run_effect _

/-- Evaluate the dropped place and resolve its glue before invoking the typed
drop call. An empty drop glue advances directly to the target. -/
def dropEffect (config : Config) (limits : Limits) (choice : C) (place : Place)
    (target : BasicBlockId) (unwind : UnwindAction) : MachineHooks.M K U Unit := do
  let checked := ExecutionMachine.withValidation config limits
  let calls := ExecutionMachine.callHooks checked limits
  let dest ← PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks checked) choice place false
  let callee ← calls.resolveDropGlue choice dest.layout.ty
  match ← calls.instanceKind callee with
  | .Shim (.DropGlue _ none) =>
    let state ← get
    let (state, outcome) := ControlFlow.goToBlock target state
    set state
    match outcome with
    | .ok value => pure value
    | .error error => throw error
  | _ => Call.initDropInPlaceCall calls choice limits.callDispatch dest.stackView callee target unwind

theorem canonical_dropEffect (config : Config) (limits : Limits) (choice : C)
    (place : Place) (target : BasicBlockId) (unwind : UnwindAction) :
    EffectSpecs.toEffect ((ExecutionMachine.terminatorHooks config limits).drop choice place target unwind) =
      dropEffect config limits choice place target unwind :=
  EffectSpecs.canonical_drop_effect _ _ _ _ _ _

attribute [spec] assertConditionEffect assertPanicEffect dropEffect

/-- Control-specific guards wrap the actual typed call, drop and assert
actions. Call dispatch remains an effect boundary for the selected callee. -/
def selectedTerminatorPre (config : Config) (limits : Limits) (choice : C) (term : Terminator)
    (post : State → Prop) (onError : Errors) (before : State) : Prop :=
  let hooks := ExecutionMachine.terminatorHooks config limits
  let checked := ExecutionMachine.withValidation config limits
  let calls := ExecutionMachine.callHooks checked limits
  match term.kind with
  | .Call _ _ _ target .. =>
    wp (Call.evalCallTerminator calls choice limits.callDispatch term) (fun _ after =>
      if target.isSome && after.stack.frames.size == before.stack.frames.size &&
          after.stack.currentFrame?.map (·.location) == before.stack.currentFrame?.map (·.location) then
        onError (.invalidProgram "evaluating this call made no progress") after
      else post after) onError before
  | .TailCall .. =>
    wp (Call.evalTailCallTerminator calls choice limits.callDispatch term) (fun _ after =>
      if after.stack.frames.size != before.stack.frames.size then
        onError (.invalidProgram "tail call changed frame index") after
      else post after) onError before
  | .Drop place target unwind _ asyncDrop =>
    if asyncDrop.isSome then
      onError (.invalidProgram "Async Drop must be expanded or reset to sync") before
    else wp (dropEffect config limits choice place target unwind) (fun _ => post) onError before
  | .Assert condition expected message target unwind =>
    let ignored := hooks.ignoreOptionalOverflowChecks before && ControlFlow.isOptionalOverflowCheck message
    wp (assertConditionEffect config limits choice condition) (fun actual after =>
      if ignored || expected == actual then InstructionWP.jumpPre target post onError after
      else wp (assertPanicEffect config limits choice message unwind) (fun _ => post) onError after)
      onError before
  | _ => InstructionWP.terminatorPreWithReturn hooks choice term (returnPre config limits choice)
      post onError before

theorem selectedTerminatorPre_iff (config : Config) (limits : Limits) (choice : C)
    (term : Terminator) (post : State → Prop) (onError : Errors) (before : State) :
    selectedTerminatorPre config limits choice term post onError before ↔
      InstructionWP.terminatorPreWithReturn (ExecutionMachine.terminatorHooks config limits)
        choice term (returnPre config limits choice) post onError before := by
  obtain ⟨info, kind⟩ := term
  cases kind <;> try rfl
  case Call => exact effectWP_iff _ _ _ _
  case TailCall => exact effectWP_iff _ _ _ _
  case Drop =>
    simp only [selectedTerminatorPre, InstructionWP.terminatorPreWithReturn]
    split
    · rfl
    · rw [← canonical_dropEffect]
      exact callbackWP_iff _ _ _ _
  case Assert =>
    simp only [selectedTerminatorPre, InstructionWP.terminatorPreWithReturn,
      ← canonical_assertCondition, ← canonical_assertPanic, callbackWP_iff]

attribute [spec] Call.evalTailCallTerminator Call.initFnTailCall Call.passArgument Panic.assertPanic assertLift

/-- Process the selected terminator after the production pre-hook. Its
successful output is the state given to the terminator continuation. -/
def terminatorPre (config : Config) (limits : Limits) (choice : C)
    (term : Terminator) (post : Success) (onError : Errors) (before : State) : Prop :=
  let checked := ExecutionMachine.withValidation config limits
  wp (TerminatorMachine.beforeTerminatorWithChoice checked.terminators (checked.preemptionChoice choice))
    (fun _ ready => selectedTerminatorPre config limits choice term (post true) onError ready) onError before

theorem terminatorPre_iff (config : Config) (limits : Limits) (choice : C)
    (term : Terminator) (post : Success) (onError : Errors) (before : State) :
    terminatorPre config limits choice term post onError before ↔
      StepWP.terminatorStepPre (ExecutionMachine.stepHooks config limits) choice term post onError before := by
  unfold terminatorPre StepWP.terminatorStepPre
  rw [effectWP_iff]
  change InstructionWP.resultPre _ _ ((ExecutionMachine.stepHooks config limits).beforeTerminator choice before) ↔ _
  rcases hook : (ExecutionMachine.stepHooks config limits).beforeTerminator choice before with ⟨ready, result⟩
  cases result with
  | error => rfl
  | ok =>
    apply (selectedTerminatorPre_iff config limits choice term (post true) onError ready).trans
    exact (InstructionWP.terminatorPreWithReturn_congr _ _ _
      (returnPre_iff config limits choice) _ _ _).trans
      (InstructionWP.terminatorPre_iff _ _ _ _ _ _)

attribute [spec] TerminatorMachine.beforeTerminatorWithChoice TerminatorMachine.maybePreemptWithChoice

/-- An already unwinding frame runs return cleanup directly. The terminator
pre-hook is only used when dispatch selected a MIR terminator. -/
def choicePre (config : Config) (limits : Limits) (choice : C)
    (post : Success) (onError : Errors) (before : State) : Prop :=
  StepWP.driverChoicePreWith
    (fun kind => statementPre config limits choice kind post onError before)
    (fun term => terminatorPre config limits choice term post onError before)
    (returnPre config limits choice true (post true) onError before)
    post onError before

theorem choicePre_iff (config : Config) (limits : Limits) (choice : C)
    (post : Success) (onError : Errors) (before : State) :
    choicePre config limits choice post onError before ↔
      StepWP.driverChoicePre (ExecutionMachine.stepHooks config limits) choice post onError before :=
  StepWP.driverChoicePreWith_congr (fun kind => statementPre_iff config limits choice kind post onError before)
    (fun term => terminatorPre_iff config limits choice term post onError before)
    ((returnPre_iff config limits choice true (post true) onError before).trans
      (InstructionWP.returnPre_iff _ _ _ _ _ _)) post onError before

/-- Require every permitted machine choice to meet the continuation, including
the resulting state of any failed prefix of an instruction. -/
def outcomePre (config : Config) (limits : Limits) (allowed : State → C → Prop)
    (post : Success) (onError : Errors) (before : State) : Prop :=
  ∀ choice, allowed before choice → choicePre config limits choice post onError before

theorem outcomePre_iff (config : Config) (limits : Limits) (allowed : State → C → Prop)
    (post : Success) (onError : Errors) (before : State) :
    outcomePre config limits allowed post onError before ↔
      ∀ after result, Step.AllowedStep (ExecutionMachine.stepHooks config limits) allowed before after result →
        InstructionWP.resultPre post onError (after, result) := by
  rw [← StepWP.driverOutcomePre_iff]
  exact forall_congr' fun choice => forall_congr' fun _ => choicePre_iff config limits choice post onError before

def stepPre (config : Config) (limits : Limits) (allowed : State → C → Prop) (more : Bool)
    (post : State → Prop) (onError : Errors) (before : State) : Prop :=
  (∃ choice, allowed before choice) ∧
    outcomePre config limits allowed (fun actual after => actual = more ∧ post after) onError before

theorem stepPre_iff (config : Config) (limits : Limits) (allowed : State → C → Prop) (more : Bool)
    (post : State → Prop) (onError : Errors) (before : State) :
    stepPre config limits allowed more post onError before ↔
      StepWP.stepPre (ExecutionMachine.stepHooks config limits) allowed more post onError before := by
  rw [StepWP.stepPre_iff_allowedStep, stepPre, outcomePre_iff]
  exact and_congr_right fun _ => forall_congr' fun _ => forall_congr' fun result =>
    forall_congr' fun _ => by cases result <;> rfl

@[spec high] theorem spec_step (config : Config) (limits : Limits) (allowed : State → C → Prop)
    (more : Bool) (post : Unit → State → Prop) (onError : Errors) :
    Triple (Program.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed) more)
      (stepPre config limits allowed more (post ()) onError) post onError :=
  Triple.iff.mpr fun before => (stepPre_iff config limits allowed more (post ()) onError before).mp

@[spec high] theorem spec_instruction (config : Config) (limits : Limits) (allowed : State → C → Prop)
    (operation : Instruction) (post : Unit → State → Prop) (onError : Errors) :
    Triple (Program.instruction (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed) operation)
      (fun before => operation.matches before ∧ stepPre config limits allowed true (post ()) onError before)
      post onError :=
  Triple.iff.mpr fun before ⟨matched, checked⟩ =>
    ⟨matched, (stepPre_iff config limits allowed true (post ()) onError before).mp checked⟩

@[spec high] theorem spec_outcomeStep (config : Config) (limits : Limits) (allowed : State → C → Prop)
    (post : Success) (onError : Errors) :
    Triple (OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed))
      (outcomePre config limits allowed post onError) post onError :=
  Triple.iff.mpr fun before checked =>
    (StepWP.driverOutcomePre_iff (ExecutionMachine.stepHooks config limits) allowed post onError before).mpr
      ((outcomePre_iff config limits allowed post onError before).mp checked)

@[spec] theorem canonical_rvalue_retagPtrValue (config : Config) (limits : Limits)
    (choice : C) (value : RvalueImmTy Miri.Memory.Provenance) (ty : TyId) :
    (ExecutionMachine.rvalueHooks config limits).retagPtrValue choice value ty =
      TypedRetag.machineRetagPtrValue (ExecutionMachine.withValidation config limits).retag
        limits.retag value ty := rfl

@[spec] theorem canonical_discriminant_writeScalar (config : Config) (choice : C)
    (value : Miri.Memory.Scalar Miri.Memory.Provenance) (dest : RuntimePlace Miri.Memory.Provenance) :
    (ExecutionMachine.discriminantHooks config).writeScalar choice value dest =
      writePlaceImmediate (ExecutionMachine.projectionHooks config).place choice (.scalar value) dest :=
  rfl

attribute [miri_rvalue] choicePre StepWP.driverChoicePreWith statementPre canonical_rvalue_retagPtrValue
  RvalueWP.evalPre RvalueWP.actionPre_bind_fun RvalueWP.actionPre_ite RvalueWP.actionPre_pure
  RvalueWP.actionPre_throw RvalueWP.canonical_placeLayout RvalueWP.canonical_readImmediate
  RvalueWP.canonical_writeImmediate RvalueWP.canonical_copyOp RvalueWP.canonical_copyOpAllowTransmute
  RvalueWP.canonical_memoryCopy RvalueWP.actionPre_rvalueHooks_withRetagMode
  EffectSpecs.canonical_rvalue_operand EffectSpecs.canonical_rvalue_place
  EffectSpecs.canonical_rvalue_placeToOp EffectSpecs.canonical_rvalue_readDiscriminant
  EffectSpecs.canonical_rvalue_discriminantForVariant EffectSpecs.canonical_rvalue_binary
  EffectSpecs.canonical_rvalue_unary EffectSpecs.canonical_rvalue_cast

end Miri.Verification.CanonicalStepWP
