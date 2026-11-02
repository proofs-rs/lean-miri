import duplicate_prefix.MetadataCalleeLeaves
import duplicate_prefix.MetadataFunctionConstant
import duplicate_prefix.CallOneArgumentAt
import duplicate_prefix.CallMoveLocal
namespace DuplicatePrefix.MetadataEvaluateCall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def argument : MIR.SpannedOperand := match SliceLenFacts.callTerminator.kind with
  | .Call _ args _ _ _ _ _ => args.getD 0 ⟨⟨0⟩,.Move ⟨2,#[]⟩⟩
  | _ => ⟨⟨0⟩,.Move ⟨2,#[]⟩⟩
theorem argument_operand : argument.operand = .Move ⟨2,#[]⟩ := by with_unfolding_all rfl
theorem disjoint : Call.moveDefinitelyDisjoint #[argument] ⟨0,#[]⟩ = true := by decide +kernel
theorem function_constant : PtrMetadataHelper.resolved.function = .Constant MetadataFunctionConstant.constant := by with_unfolding_all rfl

theorem evaluate (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (value : Immediate Provenance)
    (body : frame.body = HelperCompilerFacts.lenBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
    (located : frame.location = .mir ⟨0,2⟩)
    (valid : 2 < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate value))
    (cached : frame.locals[2].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    Call.evalCalleeAndArgs (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits)
      () PtrMetadataHelper.resolved.function #[argument] ⟨0,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok ⟨.Instance PtrMetadataHelper.resolved.callee,#[.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩],
        .Rust,some PtrMetadataHelper.abi,false⟩ (Storage.withCurrent frames frame machine) := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  let state := Storage.withCurrent frames frame machine
  have fnOp : h.evalOperandAt () (OperandPath.instruction "function") PtrMetadataHelper.resolved.function state =
      .ok ⟨.immediate .uninit,MetadataCallQueries.functionLayout⟩ state := by
    rw [function_constant]
    exact MetadataFunctionConstant.function_operand options limits remaining span source debug frames frame machine
      (congrArg (·.index) identity) located callee
  have argOp : Call.evalFnCallArgumentAt h () argument.operand (Call.moveDefinitelyDisjoint #[argument] ⟨0,#[]⟩)
      (OperandPath.argument 0) state = .ok (.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩) state := by
    rw [argument_operand,disjoint]
    exact CallMoveLocal.move_cached options limits remaining span debug frames frame machine 2 PtrMetadataHelper.rawLayout value
      valid live cached RootPointerCopy.raw_sized noClocks ghost _
  have resolve : h.resolve () 10 PtrMetadataHelper.resolved.callee.args state = .ok PtrMetadataHelper.resolved.callee state := by
    change (PreparedContracts.actualConfig options () remaining span).calls.compiler.resolve () 10 PtrMetadataHelper.resolved.callee.args state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
    exact MetadataCallQueries.resolve_current frames frame machine body identity callee located
  have fnAbi : h.fnAbiOfInstance () PtrMetadataHelper.resolved.callee #[] = pure PtrMetadataHelper.abi := by
    funext state
    exact MetadataCallFacts.actual_metadata_abi options () remaining span state
  have callerLocation : h.requiresCallerLocation PtrMetadataHelper.resolved.callee = pure false := by
    funext state
    exact MetadataCallFacts.actual_metadata_caller_location options () remaining span limits state
  exact CallOneArgumentAt.eval_callee_one_at h () PtrMetadataHelper.resolved.function argument ⟨0,#[]⟩
    ⟨.immediate .uninit,MetadataCallQueries.functionLayout⟩ state state state .Rust 10 PtrMetadataHelper.resolved.callee.args
    PtrMetadataHelper.resolved.callee 10 PtrMetadataHelper.abi false (.Copy ⟨.immediate value,PtrMetadataHelper.rawLayout⟩)
    fnOp argOp (MetadataCalleeLeaves.signature options limits remaining span cmp)
    (MetadataCalleeLeaves.kind options limits remaining span) resolve PtrMetadataHelper.callee_kind fnAbi callerLocation
end
end DuplicatePrefix.MetadataEvaluateCall
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.MetadataEvaluateCall.evaluate) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual metadata callee evaluation dependency {dependency}"
