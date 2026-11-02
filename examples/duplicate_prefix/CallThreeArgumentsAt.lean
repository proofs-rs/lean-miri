import duplicate_prefix.GenericCallStages
namespace DuplicatePrefix.CallThreeArgumentsAt
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem eval_callee_three_at
    (h : CallHooks P S C E Other Extern FnABI ArgABI) (choice : C)
    (function : Miri.MIR.Operand) (first second third : SpannedOperand) (dest : Place) (fnOp : OpTy P)
    (before afterFunction afterFirst afterSecond afterThird : S) (externAbi : Extern) (definition : DefId) (genericArgs : Array GenericArg)
    (calleeInstance : CallInstance) (item : DefId) (abi : FnABI) (requires : Bool) (arg0 arg1 arg2 : FnArg P)
    (operand : h.evalOperandAt choice (OperandPath.instruction "function") function before = .ok fnOp afterFunction)
    (firstEffect : Call.evalFnCallArgumentAt h choice first.operand (Call.moveDefinitelyDisjoint #[first,second,third] dest)
      (OperandPath.argument 0) afterFunction = .ok arg0 afterFirst)
    (secondEffect : Call.evalFnCallArgumentAt h choice second.operand (Call.moveDefinitelyDisjoint #[first,second,third] dest)
      (OperandPath.argument 1) afterFirst = .ok arg1 afterSecond)
    (thirdEffect : Call.evalFnCallArgumentAt h choice third.operand (Call.moveDefinitelyDisjoint #[first,second,third] dest)
      (OperandPath.argument 2) afterSecond = .ok arg2 afterThird)
    (signature : h.functionSignature choice fnOp.layout = pure (3,externAbi))
    (kind : h.functionKind fnOp.layout.ty = pure (.FnDef definition genericArgs))
    (resolve : h.resolve choice definition genericArgs afterThird = .ok calleeInstance afterThird)
    (itemKind : calleeInstance.kind = .Item item)
    (fnAbi : h.fnAbiOfInstance choice calleeInstance #[] = pure abi)
    (callerLocation : h.requiresCallerLocation calleeInstance = pure requires) :
    Call.evalCalleeAndArgs h choice function #[first,second,third] dest before =
      .ok ⟨.Instance calleeInstance,#[arg0,arg1,arg2],externAbi,some abi,requires⟩ afterThird := by
  simp only [Call.evalCalleeAndArgs,operand,signature,kind,resolve,itemKind,fnAbi,callerLocation,
    bind,EStateM.bind,pure,EStateM.pure]
  unfold_call_require
  simp [bind,EStateM.bind,pure,EStateM.pure,←Array.forIn_toList,
    List.range'_succ,List.forIn_cons,List.forIn_nil,firstEffect,secondEffect,thirdEffect]
  simp only [signature,kind,resolve,itemKind,fnAbi,callerLocation,pure,EStateM.pure,bind,EStateM.bind]
end DuplicatePrefix.CallThreeArgumentsAt

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.CallThreeArgumentsAt.eval_callee_three_at] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved source metadata call dependency {dependency}"
