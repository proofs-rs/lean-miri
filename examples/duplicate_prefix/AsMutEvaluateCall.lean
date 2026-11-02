import duplicate_prefix.AsMutCalleeLeaves
import duplicate_prefix.AsMutFunctionConstant
import duplicate_prefix.CallOneArgumentAt
import duplicate_prefix.CallMoveLocal
import duplicate_prefix.AsMutCallQueries
namespace DuplicatePrefix.AsMutEvaluateCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def terminator := (RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)).terminator

theorem callee_kind : HelperCompilerFacts.asMutPtrCall.callee.kind = .Item 3 := by with_unfolding_all rfl

noncomputable def argument : MIR.SpannedOperand := match terminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 0 ⟨⟨0⟩,.Move ⟨16,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨16,#[]⟩⟩
theorem argument_operand : argument.operand = .Move ⟨16,#[]⟩ := by with_unfolding_all rfl
theorem disjoint : Call.moveDefinitelyDisjoint #[argument] ⟨15,#[]⟩ = true := by decide +kernel
theorem function_constant : HelperCompilerFacts.asMutPtrCall.function = .Constant AsMutFunctionConstant.constant := by with_unfolding_all rfl

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
    (located : frame.location = .mir ⟨6,8⟩)
    (valid : 16 < frame.locals.size)
    (live : frame.locals[16].value = .live (.immediate value))
    (cached : frame.locals[16].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    Call.evalCalleeAndArgs (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () HelperCompilerFacts.asMutPtrCall.function #[argument] ⟨15,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok ⟨.Instance HelperCompilerFacts.asMutPtrCall.callee,#[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩],
        .Rust,some HelperCompilerFacts.asMutPtrAbi,false⟩ (Storage.withCurrent frames frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames frame machine
  have fnOp : h.evalOperandAt () (OperandPath.instruction "function") HelperCompilerFacts.asMutPtrCall.function state =
      .ok ⟨.immediate .uninit,AsMutFunctionFacts.functionLayout⟩ state := by
    rw [function_constant]
    exact AsMutFunctionConstant.function_operand options limits remaining span source debug frames frame machine
      (congrArg (·.index) identity) located callee
  have argOp : Call.evalFnCallArgumentAt h () argument.operand (Call.moveDefinitelyDisjoint #[argument] ⟨15,#[]⟩)
      (OperandPath.argument 0) state = .ok (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩) state := by
    rw [argument_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 16 ActualReferenceMetadata.reference value
      valid live cached ActualReferenceMetadata.reference_sized noClocks ghost _
  have resolve : h.resolve () 3 HelperCompilerFacts.asMutPtrCall.callee.args state = .ok HelperCompilerFacts.asMutPtrCall.callee state := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.resolve () 3 HelperCompilerFacts.asMutPtrCall.callee.args state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact AsMutCallQueries.resolve_current frames frame machine body identity callee located
  have fnAbi : h.fnAbiOfInstance () HelperCompilerFacts.asMutPtrCall.callee #[] = pure HelperCompilerFacts.asMutPtrAbi := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_abi options () remaining span state
  have callerLocation : h.requiresCallerLocation HelperCompilerFacts.asMutPtrCall.callee = pure false := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_caller_location options () remaining span limits state
  exact CallOneArgumentAt.eval_callee_one_at h () HelperCompilerFacts.asMutPtrCall.function argument ⟨15,#[]⟩
    ⟨.immediate .uninit,AsMutFunctionFacts.functionLayout⟩ state state state .Rust 3 HelperCompilerFacts.asMutPtrCall.callee.args
    HelperCompilerFacts.asMutPtrCall.callee 3 HelperCompilerFacts.asMutPtrAbi false (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
    fnOp argOp (AsMutCalleeLeaves.signature options limits remaining span cmp)
    (AsMutCalleeLeaves.kind options limits remaining span) resolve callee_kind fnAbi callerLocation
end
end DuplicatePrefix.AsMutEvaluateCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.AsMutEvaluateCall.evaluate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata callee evaluation dependency {dependency}"
