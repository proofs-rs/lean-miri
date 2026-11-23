import Miri.Interpreter.ControlFlow

/-! Exact continuation rules for the MIR instruction handlers. -/
namespace Miri.Verification.InstructionWP

open Miri.Interpreter Miri.MIR

variable {P L E M C V Op Imm : Type}
local notation "State" => StepState P L E M
local notation "Errors" => StepError → State → Prop
local notation "Post" => State → Prop

/-- Require the appropriate continuation at a single hook's actual output. -/
def resultPre {S A : Type} (post : A → S → Prop) (onError : StepError → S → Prop)
    (outcome : StepResult S A) : Prop :=
  match outcome with
  | (state, .ok value) => post value state
  | (state, .error error) => onError error state

/-- The statement continuation observes the frame and location after the effect. -/
def finishStatementResultPre (oldIndex : Nat) (post : Bool → State → Prop) (onError : Errors)
    (state : State) : Prop :=
  let index := state.stack.frames.size - 1
  if oldIndex != index then onError (.frameIndexChanged oldIndex index) state
  else
    match state.stack.currentFrame? with
    | none => onError (.stack .emptyStack) state
    | some current =>
      match current.location with
      | .unwinding _ => onError .expectedMirLocation state
      | .mir loc =>
        if h : index < state.stack.frames.size then
          let next := { loc with statementIndex := loc.statementIndex + 1 }
          let stack := { state.stack with frames := state.stack.frames.set index (
            { current with location := .mir next }) h }
          post true { state with stack }
        else onError (.stack .emptyStack) state

theorem finishStatementResultPre_iff (oldIndex : Nat) (post : Bool → State → Prop) (onError : Errors)
    (state : State) :
    finishStatementResultPre oldIndex post onError state ↔
      resultPre post onError
        (Step.finishStatement oldIndex (state, .ok ())) := by
  simp only [finishStatementResultPre, Step.finishStatement, Id.run]
  split
  · rfl
  · cases frame : state.stack.currentFrame? with
    | none => rfl
    | some current =>
      cases loc : current.location <;> simp only [loc]
      · split <;> rfl
      · rfl

abbrev finishStatementPre (oldIndex : Nat) (more : Bool) (post : Post) (onError : Errors) :=
  finishStatementResultPre oldIndex (fun actual state => actual = more ∧ post state) onError

theorem finishStatementPre_iff (oldIndex : Nat) (more : Bool) (post : Post) (onError : Errors)
    (state : State) :
    finishStatementPre oldIndex more post onError state ↔
      resultPre (fun actual state => actual = more ∧ post state) onError
        (Step.finishStatement oldIndex (state, .ok ())) :=
  finishStatementResultPre_iff _ _ _ _

/-- Every statement constructor, including the post-projection write for
SetDiscriminant and the projection-only effect of PlaceMention. -/
def statementPre (hooks : StepHooks P L E M C V) (choice : C) (kind : StatementKind)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  match kind with
  | .Assign place value => resultPre (fun _ => post) onError (hooks.assign choice place value state)
  | .SetDiscriminant place variant =>
    resultPre (fun dest after => resultPre (fun _ => post) onError
      (hooks.writeDiscriminant choice variant dest after))
      onError (hooks.evalPlace choice place false state)
  | .StorageLive localId => resultPre (fun _ => post) onError (hooks.storageLive choice localId state)
  | .StorageDead localId => resultPre (fun _ => post) onError (hooks.storageDead choice localId state)
  | .Intrinsic intrinsic => resultPre (fun _ => post) onError (hooks.intrinsic choice intrinsic state)
  | .PlaceMention place => resultPre (fun _ => post) onError (hooks.evalPlace choice place false state)
  | .ConstEvalCounter => resultPre (fun _ => post) onError (hooks.incrementConstEvalCounter choice state)
  | .FakeRead .. | .AscribeUserType .. | .Coverage .. | .Nop
  | .BackwardIncompatibleDropHint .. => post state

theorem statementPre_iff (hooks : StepHooks P L E M C V) (choice : C) (stmt : Statement)
    (post : Post) (onError : Errors) (state : State) :
    statementPre hooks choice stmt.kind post onError state ↔
      resultPre (fun _ => post) onError (Step.evalStatement hooks choice stmt state) := by
  obtain ⟨info, kind⟩ := stmt
  cases kind <;> try rfl
  case SetDiscriminant place variant =>
    rcases evaluated : hooks.evalPlace choice place false state with ⟨after, result⟩
    cases result <;> simp [statementPre, Step.evalStatement, evaluated, resultPre]
  case PlaceMention place =>
    rcases evaluated : hooks.evalPlace choice place false state with ⟨after, result⟩
    cases result <;> simp [statementPre, Step.evalStatement, evaluated, resultPre, Except.map]

/-- A jump requires a current frame and updates its location directly. -/
def locationPre (location : FrameLocation) (post : Post) (onError : Errors) (state : State) : Prop :=
  match state.stack.currentFrame? with
  | none => onError (.stack .emptyStack) state
  | some frame =>
    post { state with stack := ⟨state.stack.frames.pop.push { frame with location }⟩ }

abbrev jumpPre (target : BasicBlockId) :=
  @locationPre P L E M (.mir ⟨target, 0⟩)

theorem locationPre_iff (location : FrameLocation) (post : Post) (onError : Errors) (state : State) :
    locationPre location post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.setLocation state location) := by
  unfold locationPre ControlFlow.setLocation
  cases state.stack.currentFrame? <;> rfl

theorem jumpPre_iff (target : BasicBlockId) (post : Post) (onError : Errors) (state : State) :
    jumpPre target post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.goToBlock target state) :=
  locationPre_iff _ _ _ _

local notation "Controls" => ControlHooks P L E M C Op
local notation "Terminators" => TerminatorHooks P L E M C Op Imm

def unwindPre (hooks : Controls) (choice : C) (action : UnwindAction)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  match action with
  | .Cleanup block => jumpPre block post onError state
  | .Unreachable => onError (.undefinedBehavior "unwinding past a frame that does not allow unwinding") state
  | .Continue | .Terminate _ =>
    match state.stack.currentFrame? with
    | none => onError (.stack .emptyStack) state
    | some frame =>
      match hooks.bodySpan frame with
      | .error error => onError error state
      | .ok span =>
        locationPre (.unwinding span) (fun after =>
          match action with
          | .Terminate reason => resultPre (fun _ => post) onError (hooks.unwindTerminate choice reason after)
          | _ => post after) onError state

theorem unwindPre_iff (hooks : Controls) (choice : C) (action : UnwindAction)
    (post : Post) (onError : Errors) (state : State) :
    unwindPre hooks choice action post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.unwindToBlock hooks choice action state) := by
  cases action
  · simp only [unwindPre, ControlFlow.unwindToBlock, Id.run]
    split
    · simp_all [resultPre, pure, Pure.pure]
    · rename_i frame _
      cases span : hooks.bodySpan frame <;>
        simp_all [locationPre, ControlFlow.setLocation, bind, Bind.bind, pure, Pure.pure, resultPre]
  · rfl
  · simp only [unwindPre, ControlFlow.unwindToBlock, Id.run]
    split
    · simp_all [resultPre, pure, Pure.pure]
    · rename_i frame _
      cases span : hooks.bodySpan frame <;>
        simp_all [locationPre, ControlFlow.setLocation, bind, Bind.bind, pure, Pure.pure, resultPre]
  · exact jumpPre_iff _ _ _ _

def finishReturnPre (hooks : Controls) (choice : C) (unwinding : Bool) (frame : Frame P L E)
    (post : Post) (onError : Errors) (action : ReturnAction) (after : State) : Prop :=
  match action with
  | .noJump => post after
  | .noCleanup =>
    if !after.stack.frames.isEmpty || unwinding then
      onError (.invalidProgram "NoCleanup requires empty stack and normal return") after
    else post after
  | .normal =>
    match frame.returnContinuation with
    | .goto ret unwind =>
      if unwinding then unwindPre hooks choice unwind post onError after
      else match ret with
        | some block => jumpPre block post onError after
        | none => onError (.undefinedBehavior "Unreachable") after
    | .stop _ =>
      if unwinding || !after.stack.frames.isEmpty then
        onError (.invalidProgram "Stop continuation requires normal root return") after
      else post after

/-- On return, check the saved stack location before reading, then use the
popped frame to determine where to copy and which continuation to follow. -/
def returnPreWithEffects (hooks : Controls) (choice : C) (unwinding : Bool)
    (pop : (Frame P L E → State → Prop) → Errors → State → Prop)
    (cleanupEffect : Frame P L E → (ReturnAction → State → Prop) → Errors → State → Prop)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  let checked (cleanup : Bool) :=
    if unwinding != cleanup then
      onError (.invalidProgram "return/unwind cleanup assertion failed") state
    else if unwinding && state.stack.frames.size == 1 then
      onError (.undefinedBehavior "unwinding past the topmost stack frame") state
    else
      resultPre (fun value read =>
        pop (fun frame popped =>
          let clean := cleanupEffect frame (finishReturnPre hooks choice unwinding frame post onError) onError
          if unwinding then clean popped
          else resultPre (fun _ => clean) onError (hooks.copyReturn choice value frame.returnPlace popped))
          onError read)
        onError (hooks.returnOperand choice state)
  match state.stack.currentFrame? with
  | none => onError (.stack .emptyStack) state
  | some frame =>
    match frame.location with
    | .unwinding _ => checked true
    | .mir loc =>
      match frame.body.basicBlocks[loc.block]? with
      | none => onError (.invalidBlock loc.block) state
      | some block => checked block.cleanup

/-- The generic hook uses its precise output as the frame-pop boundary. -/
def returnPre (hooks : Controls) (choice : C) (unwinding : Bool)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  returnPreWithEffects hooks choice unwinding
    (fun finish failure read => resultPre finish failure (hooks.popFrame choice read))
    (fun frame finish failure popped => resultPre finish failure (hooks.cleanupFrame choice unwinding frame popped))
    post onError state

theorem returnPreWithEffects_congr (hooks : Controls) (choice : C) (unwinding : Bool)
    {pop pop' : (Frame P L E → State → Prop) → Errors → State → Prop}
    {cleanup cleanup' : Frame P L E → (ReturnAction → State → Prop) → Errors → State → Prop}
    (popEq : ∀ finish failure read, pop finish failure read ↔ pop' finish failure read)
    (cleanupEq : ∀ frame finish failure popped,
      cleanup frame finish failure popped ↔ cleanup' frame finish failure popped)
    (post : Post) (onError : Errors) (state : State) :
    returnPreWithEffects hooks choice unwinding pop cleanup post onError state ↔
      returnPreWithEffects hooks choice unwinding pop' cleanup' post onError state := by
  rw [funext fun finish => funext fun failure => funext fun read => propext (popEq finish failure read),
    funext fun frame => funext fun finish => funext fun failure => funext fun popped =>
      propext (cleanupEq frame finish failure popped)]

set_option maxHeartbeats 1000000 in
theorem returnPre_iff (hooks : Controls) (choice : C) (unwinding : Bool)
    (post : Post) (onError : Errors) (state : State) :
    returnPre hooks choice unwinding post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.returnFromCurrentFrame hooks choice unwinding state) := by
  simp only [returnPre, returnPreWithEffects, ControlFlow.returnFromCurrentFrame, Id.run, bind, Bind.bind,
    pure, Pure.pure]
  cases found : state.stack.currentFrame? with
  | none => rfl
  | some current =>
    cases location : current.location <;> simp only [location]
    case' mir loc =>
      cases selected : current.body.basicBlocks[loc.block]? <;>
        simp only <;> try rfl
    all_goals
      try dsimp only
      split
      · rfl
      · split
        · rfl
        · rcases read : hooks.returnOperand choice state with ⟨readState, readResult⟩
          cases readResult with
          | error => simp [read, resultPre]
          | ok value =>
            rcases pop : hooks.popFrame choice readState with ⟨popState, popResult⟩
            cases popResult with
            | error => simp [read, pop, resultPre]
            | ok frame =>
              simp only [read, pop, resultPre]
              cases unwinding
              · rcases copied : hooks.copyReturn choice value frame.returnPlace popState with ⟨after, result⟩
                cases result with
                | error => simp [copied]
                | ok success =>
                  cases success
                  simp only [copied, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
                  rcases cleaned : hooks.cleanupFrame choice false frame after with ⟨after, outcome⟩
                  cases outcome with
                  | error => simp [cleaned, finishReturnPre, resultPre]
                  | ok action =>
                    cases action with
                    | normal =>
                      simp only [cleaned, finishReturnPre, resultPre, Bool.false_eq_true, ↓reduceIte]
                      cases continuation : frame.returnContinuation with
                      | goto ret unwind =>
                        simp only
                        cases ret
                        · rfl
                        · exact jumpPre_iff _ _ _ _
                      | stop =>
                        simp only
                        split <;> rfl
                    | noJump => simp [cleaned, finishReturnPre, resultPre]
                    | noCleanup =>
                      simp only [cleaned, finishReturnPre, resultPre]
                      split <;> rfl
              · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rcases cleaned : hooks.cleanupFrame choice true frame popState with ⟨after, outcome⟩
                cases outcome with
                | error => simp [cleaned, finishReturnPre, resultPre]
                | ok action =>
                  cases action with
                  | normal =>
                    simp only [cleaned, finishReturnPre, resultPre, ↓reduceIte]
                    cases continuation : frame.returnContinuation with
                    | goto ret unwind =>
                      simpa only [resultPre] using unwindPre_iff hooks choice unwind post onError after
                    | stop => simp
                  | noJump => simp [cleaned, finishReturnPre, resultPre]
                  | noCleanup => simp [cleaned, finishReturnPre, resultPre]

/-- Compare cases in order, threading the state from every comparison, and
stop at the first match or error. -/
def switchCasesPre (hooks : Terminators) (choice : C) (value : Imm)
    (otherwise : BasicBlockId) (post : BasicBlockId → State → Prop) (onError : Errors) :
    List SwitchTarget → State → Prop
  | [], state => post otherwise state
  | .Case bits block :: rest, state =>
    resultPre (fun passed after =>
      if passed then post block after else switchCasesPre hooks choice value otherwise post onError rest after)
      onError (hooks.compareSwitchCase choice value bits state)

theorem switchCasesPre_iff (hooks : Terminators) (choice : C) (value : Imm)
    (targets : SwitchTargets) (post : BasicBlockId → State → Prop) (onError : Errors) (state : State) :
    switchCasesPre hooks choice value targets.otherwise post onError targets.cases.toList state ↔
      resultPre post onError (ControlFlow.selectSwitchTarget hooks choice value targets state) := by
  simp only [ControlFlow.selectSwitchTarget, Id.run, ← Array.forIn_toList]
  induction targets.cases.toList generalizing state with
  | nil => rfl
  | cons hd tail ih =>
    cases hd with
    | Case bits block =>
      simp only [switchCasesPre, List.forIn_cons, bind, Bind.bind, pure, Pure.pure]
      rcases compared : hooks.compareSwitchCase choice value bits state with ⟨after, result⟩
      cases result with
      | error => simp only [compared, resultPre]
      | ok passed =>
        cases passed
        · simp only [compared, resultPre, Bool.false_eq_true, ↓reduceIte]
          exact ih after
        · simp only [compared, resultPre, ite_true]

def switchPre (hooks : Terminators) (choice : C) (discr : Operand) (targets : SwitchTargets)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  resultPre (fun value after =>
    switchCasesPre hooks choice value targets.otherwise (fun target => jumpPre target post onError)
      onError targets.cases.toList after) onError (hooks.evalDiscriminant choice discr state)

theorem switchPre_iff (hooks : Terminators) (choice : C) (discr : Operand) (targets : SwitchTargets)
    (post : Post) (onError : Errors) (state : State) :
    switchPre hooks choice discr targets post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.evalSwitchInt hooks choice discr targets state) := by
  rcases discrResult : hooks.evalDiscriminant choice discr state with ⟨after, result⟩
  cases result with
  | error => simp [switchPre, ControlFlow.evalSwitchInt, discrResult, resultPre, Id.run, pure, Pure.pure]
  | ok value =>
    simp only [switchPre, ControlFlow.evalSwitchInt, discrResult, resultPre, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    change switchCasesPre hooks choice value targets.otherwise (fun target => jumpPre target post onError)
      onError targets.cases.toList after ↔ _
    rw [switchCasesPre_iff]
    rcases selected : ControlFlow.selectSwitchTarget hooks choice value targets after with ⟨next, outcome⟩
    cases outcome with
    | error => rfl
    | ok target => exact jumpPre_iff _ _ _ _

/-- The continuation begins after the driver's pre-terminator hook. The
selected terminator retains its original source information across that hook. -/
def terminatorPreWithReturn (hooks : Terminators) (choice : C) (term : Terminator)
    (returnFromFrame : Bool → Post → Errors → State → Prop)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  match term.kind with
  | .Goto target _ => jumpPre target post onError state
  | .Return => returnFromFrame false post onError state
  | .UnwindResume => returnFromFrame true post onError state
  | .UnwindTerminate reason => resultPre (fun _ => post) onError (hooks.unwindTerminate choice reason state)
  | .Unreachable => onError (.undefinedBehavior "Unreachable") state
  | .InlineAsm _ => onError (.unsupported "inline assembly") state
  | .FalseEdge .. | .FalseUnwind .. | .Yield .. | .CoroutineDrop =>
    onError (.invalidProgram "terminator should have been eliminated by MIR pass") state
  | .SwitchInt discr targets => switchPre hooks choice discr targets post onError state
  | .Call _ _ _ target .. =>
    resultPre (fun _ after =>
      if target.isSome && after.stack.frames.size == state.stack.frames.size &&
          after.stack.currentFrame?.map (·.location) == state.stack.currentFrame?.map (·.location) then
        onError (.invalidProgram "evaluating this call made no progress") after
      else post after) onError (hooks.call choice term state)
  | .TailCall .. =>
    resultPre (fun _ after =>
      if after.stack.frames.size != state.stack.frames.size then
        onError (.invalidProgram "tail call changed frame index") after
      else post after) onError (hooks.tailCall choice term state)
  | .Drop place target unwind _ asyncDrop =>
    if asyncDrop.isSome then onError (.invalidProgram "Async Drop must be expanded or reset to sync") state
    else resultPre (fun _ => post) onError (hooks.drop choice place target unwind state)
  | .Assert condition expected message target unwind =>
    let ignored := hooks.ignoreOptionalOverflowChecks state && ControlFlow.isOptionalOverflowCheck message
    resultPre (fun actual after =>
      if ignored || expected == actual then jumpPre target post onError after
      else resultPre (fun _ => post) onError (hooks.assertPanic choice message unwind after))
      onError (hooks.readAssertCondition choice condition state)

def terminatorPre (hooks : Terminators) (choice : C) (term : Terminator)
    (post : Post) (onError : Errors) (state : State) : Prop :=
  terminatorPreWithReturn hooks choice term (returnPre hooks.toControlHooks choice) post onError state

theorem terminatorPreWithReturn_congr (hooks : Terminators) (choice : C) (term : Terminator)
    {ret ret' : Bool → Post → Errors → State → Prop}
    (same : ∀ unwind post onError state, ret unwind post onError state ↔ ret' unwind post onError state)
    (post : Post) (onError : Errors) (state : State) :
    terminatorPreWithReturn hooks choice term ret post onError state ↔
      terminatorPreWithReturn hooks choice term ret' post onError state := by
  rw [funext fun unwind => funext fun post => funext fun onError => funext fun state =>
    propext (same unwind post onError state)]

theorem terminatorPre_iff (hooks : Terminators) (choice : C) (term : Terminator)
    (post : Post) (onError : Errors) (state : State) :
    terminatorPre hooks choice term post onError state ↔
      resultPre (fun _ => post) onError (ControlFlow.evalTerminator hooks choice term state) := by
  obtain ⟨info, kind⟩ := term
  cases kind <;> simp only [terminatorPre, terminatorPreWithReturn, ControlFlow.evalTerminator, Id.run, pure, Pure.pure] <;> try rfl
  case Goto => exact jumpPre_iff _ _ _ _
  case Return => exact returnPre_iff _ _ _ _ _ _
  case UnwindResume => exact returnPre_iff _ _ _ _ _ _
  case SwitchInt => exact switchPre_iff _ _ _ _ _ _ _
  case Call fn args dest target unwind source span =>
    let term : Terminator := ⟨info, .Call fn args dest target unwind source span⟩
    change resultPre _ onError (hooks.call choice term state) ↔
      resultPre (fun _ => post) onError (ControlFlow.evalCall hooks choice term target state)
    rcases called : hooks.call choice term state with ⟨after, result⟩
    cases result with
    | error => simp [ControlFlow.evalCall, called, resultPre, Id.run, pure, Pure.pure]
    | ok success =>
      cases success
      simp only [ControlFlow.evalCall, called, Id.run, pure, Pure.pure, resultPre]
      split <;> rfl
  case TailCall fn args span =>
    rcases called : hooks.tailCall choice ⟨info, .TailCall fn args span⟩ state with ⟨after, result⟩
    cases result with
    | error => simp [called, resultPre]
    | ok success =>
      cases success
      simp only [called, resultPre]
      split <;> rfl
  case Drop =>
    simp only [ControlFlow.evalDrop, Id.run, pure, Pure.pure]
    split <;> rfl
  case Assert condition expected message target unwind =>
    rcases read : hooks.readAssertCondition choice condition state with ⟨after, result⟩
    cases result with
    | error => simp [ControlFlow.evalAssert, read, resultPre, Id.run, pure, Pure.pure]
    | ok actual =>
      simp only [ControlFlow.evalAssert, read, Id.run, pure, Pure.pure, resultPre]
      split
      · exact jumpPre_iff _ _ _ _
      · rfl

end Miri.Verification.InstructionWP
