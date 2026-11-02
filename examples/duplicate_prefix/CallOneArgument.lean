import duplicate_prefix.GenericCallStages
namespace DuplicatePrefix.CallOneArgument
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem eval_callee_one
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (function : Miri.MIR.Operand) (argument : SpannedOperand) (dest : Place) (fnOp : OpTy P)
    (before afterFunction afterArgument : S) (externAbi : Extern) (definition : DefId) (genericArgs : Array GenericArg)
    (calleeInstance : CallInstance) (item : DefId) (abi : FnABI) (requires : Bool) (arg : FnArg P)
    (operand : h.evalOperandAt choice (OperandPath.instruction "function") function before = .ok fnOp afterFunction)
    (argumentEffect : Call.evalFnCallArgumentAt h choice argument.operand (Call.moveDefinitelyDisjoint #[argument] dest)
      (OperandPath.argument 0) afterFunction = .ok arg afterArgument)
    (signature : h.functionSignature choice fnOp.layout = pure (1,externAbi))
    (kind : h.functionKind fnOp.layout.ty = pure (.FnDef definition genericArgs))
    (resolve : h.resolve choice definition genericArgs = pure calleeInstance)
    (itemKind : calleeInstance.kind = .Item item)
    (fnAbi : h.fnAbiOfInstance choice calleeInstance #[] = pure abi)
    (callerLocation : h.requiresCallerLocation calleeInstance = pure requires) :
    Call.evalCalleeAndArgs h choice function #[argument] dest before =
      .ok ⟨.Instance calleeInstance,#[arg],externAbi,some abi,requires⟩ afterArgument := by
  simp only [Call.evalCalleeAndArgs,operand,signature,kind,resolve,itemKind,fnAbi,callerLocation,
    bind,EStateM.bind,pure,EStateM.pure]
  unfold_call_require
  simp [bind,EStateM.bind,pure,EStateM.pure,←Array.forIn_toList,
    List.range'_succ,List.forIn_cons,List.forIn_nil,argumentEffect]
  simp only [signature,kind,resolve,itemKind,fnAbi,callerLocation,pure,EStateM.pure,bind,EStateM.bind]
theorem move_immediate
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C) (place : Place) (path : OperandPath)
    (before cached after : S) (destination : RuntimeStackPlace P) (value : Immediate P) (layout : LocalLayout)
    (evaluated : h.evalPlace choice place true before = .ok destination cached)
    (read : h.placeToOp choice destination cached = .ok ⟨.immediate value,layout⟩ after) :
    Call.evalFnCallArgumentAt h choice (.Move place) true path before =
      .ok (.Copy ⟨.immediate value,layout⟩) after := by
  simp [Call.evalFnCallArgumentAt, evaluated,read,bind,EStateM.bind,pure,EStateM.pure]
end DuplicatePrefix.CallOneArgument
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CallOneArgument.eval_callee_one, ``DuplicatePrefix.CallOneArgument.move_immediate] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved one-argument call dependency {dependency}"
