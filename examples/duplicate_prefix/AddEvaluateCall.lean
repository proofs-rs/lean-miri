import duplicate_prefix.AddCalleeLeaves
import duplicate_prefix.AddFunctionConstant
import duplicate_prefix.CallTwoArgumentsAt
import duplicate_prefix.CallMoveLocal
import duplicate_prefix.AddCallQueries
import duplicate_prefix.PointerArgumentCopy
namespace DuplicatePrefix.AddEvaluateCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def terminator := (RootBody.reflected.body.body.basicBlocks[7]'(by with_unfolding_all decide +kernel)).terminator

theorem callee_kind : HelperCompilerFacts.addCall.callee.kind = .Item 4 := by with_unfolding_all rfl

noncomputable def argument0 : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 0 ⟨⟨0⟩,.Move ⟨22,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨22,#[]⟩⟩
noncomputable def argument1 : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 1 ⟨⟨0⟩,.Move ⟨23,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨23,#[]⟩⟩
theorem argument0_operand : argument0.operand = .Move ⟨22,#[]⟩ := by with_unfolding_all rfl
theorem argument1_operand : argument1.operand = .Move ⟨23,#[]⟩ := by with_unfolding_all rfl
theorem disjoint : Call.moveDefinitelyDisjoint #[argument0,argument1] ⟨21,#[]⟩ = true := by decide +kernel
theorem function_constant : HelperCompilerFacts.addCall.function = .Constant AddFunctionConstant.constant := by with_unfolding_all rfl

theorem evaluate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Scalar Provenance) (n : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨7,13⟩)
    (valid22 : 22 < frame.locals.size) (valid23 : 23 < frame.locals.size)
    (live22 : frame.locals[22].value = .live (.immediate (.scalar pointer)))
    (cached22 : frame.locals[22].layout = some CopyCompilerFacts.destPointerLayout)
    (live23 : frame.locals[23].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached23 : frame.locals[23].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    Call.evalCalleeAndArgs (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () HelperCompilerFacts.addCall.function #[argument0,argument1] ⟨21,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok ⟨.Instance HelperCompilerFacts.addCall.callee,#[.Copy ⟨.immediate (.scalar pointer),CopyCompilerFacts.destPointerLayout⟩,.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩],
        .Rust,some HelperCompilerFacts.addAbi,true⟩ (Storage.withCurrent frames frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames frame machine
  have fnOp : h.evalOperandAt () (OperandPath.instruction "function") HelperCompilerFacts.addCall.function state =
      .ok ⟨.immediate .uninit,AddFunctionFacts.functionLayout⟩ state := by
    rw [function_constant]
    exact AddFunctionConstant.function_operand options limits remaining span source debug frames frame machine
      (congrArg (·.index) identity) located callee
  have arg0 : Call.evalFnCallArgumentAt h () argument0.operand (Call.moveDefinitelyDisjoint #[argument0,argument1] ⟨21,#[]⟩)
      (OperandPath.argument 0) state = .ok (.Copy ⟨.immediate (.scalar pointer),CopyCompilerFacts.destPointerLayout⟩) state := by
    rw [argument0_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 22 CopyCompilerFacts.destPointerLayout (.scalar pointer)
      valid22 live22 cached22 RootRawPointerValidity.mut_pointer_sized noClocks ghost _
  have arg1 : Call.evalFnCallArgumentAt h () argument1.operand (Call.moveDefinitelyDisjoint #[argument0,argument1] ⟨21,#[]⟩)
      (OperandPath.argument 1) state = .ok (.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩) state := by
    rw [argument1_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 23 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 n)))
      valid23 live23 cached23 (by decide +kernel) noClocks ghost _
  have resolve : h.resolve () 4 HelperCompilerFacts.addCall.callee.args state = .ok HelperCompilerFacts.addCall.callee state := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.resolve () 4 HelperCompilerFacts.addCall.callee.args state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact AddCallQueries.resolve_current frames frame machine body identity callee located
  have fnAbi : h.fnAbiOfInstance () HelperCompilerFacts.addCall.callee #[] = pure HelperCompilerFacts.addAbi := by
    funext state
    exact AddCallFacts.actual_add_abi options () remaining span state
  have callerLocation : h.requiresCallerLocation HelperCompilerFacts.addCall.callee = pure true := by
    funext state
    exact AddCallFacts.actual_add_caller_location options () remaining span limits state
  exact CallTwoArgumentsAt.eval_callee_two_at h () HelperCompilerFacts.addCall.function argument0 argument1 ⟨21,#[]⟩
    ⟨.immediate .uninit,AddFunctionFacts.functionLayout⟩ state state state state .Rust 4 HelperCompilerFacts.addCall.callee.args
    HelperCompilerFacts.addCall.callee 4 HelperCompilerFacts.addAbi true (.Copy ⟨.immediate (.scalar pointer),CopyCompilerFacts.destPointerLayout⟩)
    (.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩)
    fnOp arg0 arg1 (AddCalleeLeaves.signature options limits remaining span cmp)
    (AddCalleeLeaves.kind options limits remaining span) resolve callee_kind fnAbi callerLocation

end
end DuplicatePrefix.AddEvaluateCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AddEvaluateCall.evaluate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata callee evaluation dependency {dependency}"
