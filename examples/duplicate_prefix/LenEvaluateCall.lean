import duplicate_prefix.LenCalleeLeaves
import duplicate_prefix.LenCallSource
import duplicate_prefix.LenArgumentCopy
import duplicate_prefix.LenFunctionConstant
import duplicate_prefix.CallOneArgumentAt
import duplicate_prefix.CallMoveLocal
namespace DuplicatePrefix.LenEvaluateCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def argument : MIR.SpannedOperand := match LenCallSource.callTerminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 0 ⟨⟨0⟩,.Move ⟨12,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨12,#[]⟩⟩
theorem argument_operand : argument.operand = .Move ⟨12,#[]⟩ := by with_unfolding_all rfl
theorem disjoint : Call.moveDefinitelyDisjoint #[argument] ⟨11,#[]⟩ = true := by decide +kernel
theorem function_constant : LenHelper.resolved.function = .Constant LenFunctionConstant.constant := by with_unfolding_all rfl

theorem evaluate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨2,12⟩)
    (valid : 12 < frame.locals.size)
    (live : frame.locals[12].value = .live (.immediate value))
    (cached : frame.locals[12].layout = some LenHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    Call.evalCalleeAndArgs (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () LenHelper.resolved.function #[argument] ⟨11,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok ⟨.Instance LenHelper.resolved.callee,#[.Copy ⟨.immediate value,LenHelper.rawLayout⟩],
        .Rust,some LenHelper.abi,false⟩ (Storage.withCurrent frames frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames frame machine
  have fnOp : h.evalOperandAt () (OperandPath.instruction "function") LenHelper.resolved.function state =
      .ok ⟨.immediate .uninit,LenCallQueries.functionLayout⟩ state := by
    rw [function_constant]
    exact LenFunctionConstant.function_operand options limits remaining span source debug frames frame machine
      (congrArg (·.index) identity) located callee
  have argOp : Call.evalFnCallArgumentAt h () argument.operand (Call.moveDefinitelyDisjoint #[argument] ⟨11,#[]⟩)
      (OperandPath.argument 0) state = .ok (.Copy ⟨.immediate value,LenHelper.rawLayout⟩) state := by
    rw [argument_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 12 LenHelper.rawLayout value
      valid live cached LenArgumentCopy.shared_sized noClocks ghost _
  have resolve : h.resolve () 1 LenHelper.resolved.callee.args state = .ok LenHelper.resolved.callee state := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.resolve () 1 LenHelper.resolved.callee.args state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact LenCallQueries.resolve_current frames frame machine body identity callee located
  have fnAbi : h.fnAbiOfInstance () LenHelper.resolved.callee #[] = pure LenHelper.abi := by
    funext state
    exact LenCallFacts.actual_len_abi options () remaining span state
  have callerLocation : h.requiresCallerLocation LenHelper.resolved.callee = pure false := by
    funext state
    exact LenCallFacts.actual_len_caller_location options () remaining span limits state
  exact CallOneArgumentAt.eval_callee_one_at h () LenHelper.resolved.function argument ⟨11,#[]⟩
    ⟨.immediate .uninit,LenCallQueries.functionLayout⟩ state state state .Rust 1 LenHelper.resolved.callee.args
    LenHelper.resolved.callee 1 LenHelper.abi false (.Copy ⟨.immediate value,LenHelper.rawLayout⟩)
    fnOp argOp (LenCalleeLeaves.signature options limits remaining span cmp)
    (LenCalleeLeaves.kind options limits remaining span) resolve LenHelper.callee_kind fnAbi callerLocation
end
end DuplicatePrefix.LenEvaluateCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.LenEvaluateCall.evaluate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata callee evaluation dependency {dependency}"
