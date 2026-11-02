import Miri.Interpreter.Call
import duplicate_prefix.StepFacts
import duplicate_prefix.StepAssembly
import duplicate_prefix.CanonicalConfigFacts
namespace DuplicatePrefix.GenericCallStages
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab Tactic in
elab "unfold_call_require" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".Call.require" then some (mkIdent name) else none
  match found with
  | [name] => evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected exact source Call.require"

theorem eval_callee_zero
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (function : Miri.MIR.Operand) (dest : Place) (fnOp : OpTy P)
    (before after : S) (externAbi : Extern) (definition : DefId) (genericArgs : Array GenericArg)
    (calleeInstance : CallInstance) (item : DefId) (abi : FnABI) (requires : Bool)
    (operand : h.evalOperandAt choice (OperandPath.instruction "function") function before = .ok fnOp after)
    (signature : h.functionSignature choice fnOp.layout = pure (0,externAbi))
    (kind : h.functionKind fnOp.layout.ty = pure (.FnDef definition genericArgs))
    (resolve : h.resolve choice definition genericArgs after = .ok calleeInstance after)
    (itemKind : calleeInstance.kind = .Item item)
    (fnAbi : h.fnAbiOfInstance choice calleeInstance #[] = pure abi)
    (callerLocation : h.requiresCallerLocation calleeInstance = pure requires) :
    Call.evalCalleeAndArgs h choice function #[] dest before =
      .ok ⟨.Instance calleeInstance,#[],externAbi,some abi,requires⟩ after := by
  simp only [Call.evalCalleeAndArgs,operand,signature,kind,resolve,itemKind,fnAbi,callerLocation,
    bind,EStateM.bind,pure,EStateM.pure]
  unfold_call_require
  simp [bind,EStateM.bind,pure,EStateM.pure,←Array.forIn_toList]
  simp only [signature,kind,resolve,itemKind,fnAbi,callerLocation,pure,EStateM.pure,bind,EStateM.bind]

theorem call_terminator
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (fuel : Nat)
    (terminator : Terminator) (function : Miri.MIR.Operand) (args : Array SpannedOperand)
    (place : Place) (target : BasicBlockId) (unwindAction : UnwindAction)
    (sourceKind : CallSource) (fnSpan : SpanRef)
    (before cached evaluated after : S) (frame : Frame P LocalLayout E)
    (oldIndex newIndex : Nat) (dest : RuntimeStackPlace P)
    (call : EvaluatedCall P Other Extern FnABI)
    (kindEq : terminator.kind = .Call function args place (some target) unwindAction sourceKind fnSpan)
    (oldFrame : h.getFrame before = .ok frame before)
    (oldFrameIndex : h.frameIndex before = .ok oldIndex before)
    (destination : h.evalPlace choice place false before = .ok dest cached)
    (callee : Call.evalCalleeAndArgs h choice function args place cached = .ok call evaluated)
    (entry : Call.initFnCall h choice fuel
      ⟨call.callee,call.callerAbi,call.fnAbi,call.args,call.withCallerLocation,dest,some target,
        if call.fnAbi.any h.abiCanUnwind then unwindAction else .Unreachable⟩ evaluated = .ok () after)
    (newFrameIndex : h.frameIndex after = .ok newIndex after)
    (progress : newIndex ≠ oldIndex) :
    Call.evalCallTerminator h choice fuel terminator before = .ok () after := by
  simp [Call.evalCallTerminator,kindEq,oldFrame,oldFrameIndex,destination,callee,entry,newFrameIndex,
    progress,bind,EStateM.bind,pure,EStateM.pure]

theorem call_hooks_validated [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host) (limits : ExecutionMachine.Limits) :
    ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits =
      ExecutionMachine.callHooks config limits := by
  unfold ExecutionMachine.callHooks
  rw [StepAssembly.with_validation_twice]

theorem control_call
    (hooks : TerminatorHooks P LayoutTy E Machine Choice Op Imm) (choice : Choice)
    (terminator : Terminator) (function : Miri.MIR.Operand) (args : Array SpannedOperand) (dest : Place)
    (target : Option BasicBlockId) (unwindAction : UnwindAction) (sourceKind : CallSource) (fnSpan : SpanRef)
    (before after : StepState P LayoutTy E Machine)
    (kindEq : terminator.kind = .Call function args dest target unwindAction sourceKind fnSpan)
    (effect : hooks.call choice terminator before = (after,.ok ()))
    (progress : after.stack.frames.size ≠ before.stack.frames.size) :
    ControlFlow.evalTerminator hooks choice terminator before = (after,.ok ()) := by
  unfold ControlFlow.evalTerminator
  rw [kindEq]
  simp [effect,progress]

theorem source_step [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host) (limits : ExecutionMachine.Limits)
    (choice : Choice) (before accounted after : MachineHooks.State K User)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (location : Location) (block : BasicBlock)
    (function : Miri.MIR.Operand) (args : Array SpannedOperand) (dest : Place)
    (target : Option BasicBlockId) (unwindAction : UnwindAction) (sourceKind : CallSource) (fnSpan : SpanRef)
    (current : before.stack.currentFrame? = some frame) (located : frame.location = .mir location)
    (blockAt : frame.body.basicBlocks[location.block]? = some block)
    (noStatement : block.statements[location.statementIndex]? = none)
    (kindEq : block.terminator.kind = .Call function args dest target unwindAction sourceKind fnSpan)
    (accounting : (ExecutionMachine.stepHooks config limits).beforeTerminator choice before = (accounted,.ok ()))
    (effect : Call.evalCallTerminator (ExecutionMachine.callHooks config limits)
      choice limits.callDispatch block.terminator accounted = .ok () after)
    (progress : after.stack.frames.size ≠ accounted.stack.frames.size) :
    ExecutionMachine.step config limits choice before = (after,.ok true) := by
  have operation : (ExecutionMachine.stepHooks config limits).terminator choice block.terminator accounted =
      (after,.ok ()) := by
    change ControlFlow.evalTerminator _ choice block.terminator accounted = _
    apply control_call _ choice block.terminator function args dest target unwindAction sourceKind fnSpan
      accounted after kindEq _ progress
    change MachineHooks.run (Call.evalCallTerminator
      (ExecutionMachine.callHooks (ExecutionMachine.withValidation config limits) limits)
      choice limits.callDispatch block.terminator) accounted = _
    rw [call_hooks_validated]
    unfold MachineHooks.run Call.run
    rw [effect]
  exact StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) choice before accounted after
    frame location block current located blockAt noStatement accounting operation

#print axioms source_step
#print axioms eval_callee_zero
#print axioms call_terminator
end DuplicatePrefix.GenericCallStages
