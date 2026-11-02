import duplicate_prefix.AsMutCallFacts
import duplicate_prefix.RootCallCore

/-! Exact source reduction of as_mut_ptr initStackFrame to its ordinary argument
initialization. The actual compiler queries are discharged; destination
protection, retag scope, all argument/count checks and full-stop cleanup remain. -/
namespace DuplicatePrefix.AsMutCallCore
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
  h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry do
    spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 1)
    let ty ← h.localLayout () 1
    Call.passArgument h () (.Copy first) (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret)
      (HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret) 0 ⟨1, #[]⟩ ty.ty false
    pure (1, 1)
  spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.asMutPtrAbi.ret HelperCompilerFacts.asMutPtrAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == HelperCompilerFacts.asMutPtrAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first : OpTy Provenance) (destination : RuntimeStackPlace Provenance) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy first] false destination (.goto (some 7) .Continue) =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation HelperCompilerFacts.asMutPtrCall.callee = pure false := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () HelperCompilerFacts.asMutPtrCall.callee #[] = pure HelperCompilerFacts.asMutPtrAbi := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_abi options () remaining span state
  have features : h.checkTargetFeatures () HelperCompilerFacts.asMutPtrCall.callee = pure () := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrAbi = pure false := by
    funext state
    exact AsMutCallFacts.actual_as_mut_ptr_noncapturing options () remaining span limits state
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.asMutPtrAbi = true := AsMutCallFacts.abi_flags.2.1
  have variadic : h.abiVariadic HelperCompilerFacts.asMutPtrAbi = false := AsMutCallFacts.abi_flags.1
  have conv : h.sameConvention HelperCompilerFacts.asMutPtrAbi HelperCompilerFacts.asMutPtrAbi = true := by
    change (HelperCompilerFacts.asMutPtrAbi.conv == HelperCompilerFacts.asMutPtrAbi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs HelperCompilerFacts.asMutPtrAbi = HelperCompilerFacts.asMutPtrAbi.args := rfl
  have ret : h.abiReturn HelperCompilerFacts.asMutPtrAbi = HelperCompilerFacts.asMutPtrAbi.ret := rfl
  have get0 : HelperCompilerFacts.asMutPtrAbi.args.getD 0 HelperCompilerFacts.asMutPtrAbi.ret = HelperCompilerFacts.asMutPtrAbi.args[0]'(by rw [AsMutCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_internal ".Call.require"
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, canUnwind, conv, args,
    AsMutCallFacts.body_flags.1, AsMutCallFacts.body_flags.2,
    AsMutCallFacts.abi_flags.2.2, ret, get0, spanAt, require,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout =>
    cases operand <;> rfl
end DuplicatePrefix.AsMutCallCore


open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AsMutCallCore." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
