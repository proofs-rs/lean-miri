import duplicate_prefix.MetadataCallFacts
import duplicate_prefix.RootCallCore

/-! Exact source reduction of root initStackFrame to its two ordinary argument
initializations. The actual compiler queries are discharged; destination
protection, retag scope, all argument/count checks and full-stop cleanup remain. -/
namespace DuplicatePrefix.MetadataCallCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev RootHooks := CallHooks Provenance RootState Unit MachineHooks.FrameExtra Unit ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
noncomputable def require (condition : Bool) (message : String) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit :=
  unless condition do throw (.invalidProgram message)

noncomputable def spanAt (h : RootHooks) (span : SpanRef) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let frame ← h.getFrame
  h.setFrame {frame with location := .unwinding span}

noncomputable def core (h : RootHooks) (first : OpTy Provenance) (destination : RuntimeStackPlace Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationOp ← h.placeToOp () destination
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  h.pushRaw () PtrMetadataHelper.resolved.callee PtrMetadataHelper.body destination (.goto (some 1) .Continue)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry do
    spanAt h (← h.localSpan PtrMetadataHelper.body.body 1)
    let ty ← h.localLayout () 1
    Call.passArgument h () (.Copy first) (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret)
      (PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret) 0 ⟨1, #[]⟩ ty.ty false
    pure (1, 1)
  spanAt h (← h.localSpan PtrMetadataHelper.body.body 0)
  unless ← h.checkArgumentCompat () PtrMetadataHelper.abi.ret PtrMetadataHelper.abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == PtrMetadataHelper.abi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first : OpTy Provenance) (destination : RuntimeStackPlace Provenance) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      PtrMetadataHelper.resolved.callee PtrMetadataHelper.body PtrMetadataHelper.abi
      #[.Copy first] false destination (.goto (some 1) .Continue) =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation PtrMetadataHelper.resolved.callee = pure false := by
    funext state
    exact MetadataCallFacts.actual_metadata_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () PtrMetadataHelper.resolved.callee #[] = pure PtrMetadataHelper.abi := by
    funext state
    exact MetadataCallFacts.actual_metadata_abi options () remaining span state
  have features : h.checkTargetFeatures () PtrMetadataHelper.resolved.callee = pure () := by
    funext state
    exact MetadataCallFacts.actual_metadata_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () PtrMetadataHelper.resolved.callee PtrMetadataHelper.abi = pure false := by
    funext state
    exact MetadataCallFacts.actual_metadata_noncapturing options () remaining span limits state
  have canUnwind : h.abiCanUnwind PtrMetadataHelper.abi = true := MetadataCallFacts.abi_flags.2.1
  have variadic : h.abiVariadic PtrMetadataHelper.abi = false := MetadataCallFacts.abi_flags.1
  have conv : h.sameConvention PtrMetadataHelper.abi PtrMetadataHelper.abi = true := by
    change (PtrMetadataHelper.abi.conv == PtrMetadataHelper.abi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs PtrMetadataHelper.abi = PtrMetadataHelper.abi.args := rfl
  have ret : h.abiReturn PtrMetadataHelper.abi = PtrMetadataHelper.abi.ret := rfl
  have get0 : PtrMetadataHelper.abi.args.getD 0 PtrMetadataHelper.abi.ret = PtrMetadataHelper.abi.args[0]'(by rw [MetadataCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_internal ".Call.require"
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, canUnwind, conv, args,
    MetadataCallFacts.body_flags.1, MetadataCallFacts.body_flags.2,
    MetadataCallFacts.abi_flags.2.2, ret, get0, spanAt, require,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout =>
    cases operand <;> rfl
end DuplicatePrefix.MetadataCallCore


open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.MetadataCallCore." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
