import duplicate_prefix.CopyCalleeLeaves
import duplicate_prefix.CopyFunctionConstant
import duplicate_prefix.CallThreeArgumentsAt
import duplicate_prefix.CallMoveLocal
import duplicate_prefix.CopyCallQueries
import duplicate_prefix.PointerArgumentCopy
namespace DuplicatePrefix.CopyEvaluateCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def terminator := (RootBody.reflected.body.body.basicBlocks[8]'(by with_unfolding_all decide +kernel)).terminator

theorem callee_kind : HelperCompilerFacts.copyCall.callee.kind = .Item 5 := by with_unfolding_all rfl

noncomputable def argument0 : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 0 ⟨⟨0⟩,.Move ⟨19,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨19,#[]⟩⟩
noncomputable def argument1 : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 1 ⟨⟨0⟩,.Move ⟨21,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨21,#[]⟩⟩
noncomputable def argument2 : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 2 ⟨⟨0⟩,.Move ⟨24,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨24,#[]⟩⟩
theorem argument0_operand : argument0.operand = .Move ⟨19,#[]⟩ := by with_unfolding_all rfl
theorem argument1_operand : argument1.operand = .Move ⟨21,#[]⟩ := by with_unfolding_all rfl
theorem argument2_operand : argument2.operand = .Move ⟨24,#[]⟩ := by with_unfolding_all rfl
theorem disjoint : Call.moveDefinitelyDisjoint #[argument0,argument1,argument2] ⟨18,#[]⟩ = true := by decide +kernel
theorem function_constant : HelperCompilerFacts.copyCall.function = .Constant CopyFunctionConstant.constant := by with_unfolding_all rfl

theorem evaluate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir ⟨8,4⟩)
    (valid19 : 19 < frame.locals.size) (valid21 : 21 < frame.locals.size) (valid24 : 24 < frame.locals.size)
    (live19 : frame.locals[19].value = .live (.immediate (.scalar sourcePointer)))
    (cached19 : frame.locals[19].layout = some CopyCompilerFacts.sourcePointerLayout)
    (live21 : frame.locals[21].value = .live (.immediate (.scalar destinationPointer)))
    (cached21 : frame.locals[21].layout = some CopyCompilerFacts.destPointerLayout)
    (live24 : frame.locals[24].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))))
    (cached24 : frame.locals[24].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    Call.evalCalleeAndArgs (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () HelperCompilerFacts.copyCall.function #[argument0,argument1,argument2] ⟨18,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok ⟨.Instance HelperCompilerFacts.copyCall.callee,#[.Copy ⟨.immediate (.scalar sourcePointer),CopyCompilerFacts.sourcePointerLayout⟩,.Copy ⟨.immediate (.scalar destinationPointer),CopyCompilerFacts.destPointerLayout⟩,.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩],
        .Rust,some HelperCompilerFacts.copyAbi,true⟩ (Storage.withCurrent frames frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames frame machine
  have fnOp : h.evalOperandAt () (OperandPath.instruction "function") HelperCompilerFacts.copyCall.function state =
      .ok ⟨.immediate .uninit,CopyFunctionFacts.functionLayout⟩ state := by
    rw [function_constant]
    exact CopyFunctionConstant.function_operand options limits remaining span source debug frames frame machine
      (congrArg (·.index) identity) located callee
  have arg0 : Call.evalFnCallArgumentAt h () argument0.operand (Call.moveDefinitelyDisjoint #[argument0,argument1,argument2] ⟨18,#[]⟩)
      (OperandPath.argument 0) state = .ok (.Copy ⟨.immediate (.scalar sourcePointer),CopyCompilerFacts.sourcePointerLayout⟩) state := by
    rw [argument0_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 19 CopyCompilerFacts.sourcePointerLayout (.scalar sourcePointer)
      valid19 live19 cached19 RootRawPointerValidity.const_pointer_sized noClocks ghost _
  have arg1 : Call.evalFnCallArgumentAt h () argument1.operand (Call.moveDefinitelyDisjoint #[argument0,argument1,argument2] ⟨18,#[]⟩)
      (OperandPath.argument 1) state = .ok (.Copy ⟨.immediate (.scalar destinationPointer),CopyCompilerFacts.destPointerLayout⟩) state := by
    rw [argument1_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 21 CopyCompilerFacts.destPointerLayout (.scalar destinationPointer)
      valid21 live21 cached21 RootRawPointerValidity.mut_pointer_sized noClocks ghost _
  have arg2 : Call.evalFnCallArgumentAt h () argument2.operand (Call.moveDefinitelyDisjoint #[argument0,argument1,argument2] ⟨18,#[]⟩)
      (OperandPath.argument 2) state = .ok (.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩) state := by
    rw [argument2_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 24 RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 n)))
      valid24 live24 cached24 (by decide +kernel) noClocks ghost _
  have resolve : h.resolve () 5 HelperCompilerFacts.copyCall.callee.args state = .ok HelperCompilerFacts.copyCall.callee state := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.resolve () 5 HelperCompilerFacts.copyCall.callee.args state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact CopyCallQueries.resolve_current frames frame machine body identity callee located
  have fnAbi : h.fnAbiOfInstance () HelperCompilerFacts.copyCall.callee #[] = pure HelperCompilerFacts.copyAbi := by
    funext state
    exact CopyCallFacts.actual_copy_abi options () remaining span state
  have callerLocation : h.requiresCallerLocation HelperCompilerFacts.copyCall.callee = pure true := by
    funext state
    exact CopyCallFacts.actual_copy_caller_location options () remaining span limits state
  exact CallThreeArgumentsAt.eval_callee_three_at h () HelperCompilerFacts.copyCall.function argument0 argument1 argument2 ⟨18,#[]⟩
    ⟨.immediate .uninit,CopyFunctionFacts.functionLayout⟩ state state state state state .Rust 5 HelperCompilerFacts.copyCall.callee.args
    HelperCompilerFacts.copyCall.callee 5 HelperCompilerFacts.copyAbi true (.Copy ⟨.immediate (.scalar sourcePointer),CopyCompilerFacts.sourcePointerLayout⟩)
    (.Copy ⟨.immediate (.scalar destinationPointer),CopyCompilerFacts.destPointerLayout⟩)
    (.Copy ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 n))),RootCompilerFacts.usizeLayout⟩)
    fnOp arg0 arg1 arg2 (CopyCalleeLeaves.signature options limits remaining span cmp)
    (CopyCalleeLeaves.kind options limits remaining span) resolve callee_kind fnAbi callerLocation

end
end DuplicatePrefix.CopyEvaluateCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyEvaluateCall.evaluate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata callee evaluation dependency {dependency}"
