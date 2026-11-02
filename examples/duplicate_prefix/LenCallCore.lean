import duplicate_prefix.LenCallFacts
import duplicate_prefix.RootCallCore

/-! Source reduction of the slice-length helper call to its single reference
argument, return ABI checks, and frame initialization. -/
namespace DuplicatePrefix.LenCallCore
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
  h.pushRaw () LenHelper.resolved.callee LenHelper.body destination (.goto (some 3) .Continue)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry do
    spanAt h (← h.localSpan LenHelper.body.body 1)
    let ty ← h.localLayout () 1
    Call.passArgument h () (.Copy first) (LenHelper.abi.args.getD 0 LenHelper.abi.ret)
      (LenHelper.abi.args.getD 0 LenHelper.abi.ret) 0 ⟨1, #[]⟩ ty.ty false
    pure (1, 1)
  spanAt h (← h.localSpan LenHelper.body.body 0)
  unless ← h.checkArgumentCompat () LenHelper.abi.ret LenHelper.abi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == LenHelper.abi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first : OpTy Provenance) (destination : RuntimeStackPlace Provenance) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi
      #[.Copy first] false destination (.goto (some 3) .Continue) =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation LenHelper.resolved.callee = pure false := by
    funext state
    exact LenCallFacts.actual_len_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () LenHelper.resolved.callee #[] = pure LenHelper.abi := by
    funext state
    exact LenCallFacts.actual_len_abi options () remaining span state
  have features : h.checkTargetFeatures () LenHelper.resolved.callee = pure () := by
    funext state
    exact LenCallFacts.actual_len_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () LenHelper.resolved.callee LenHelper.abi = pure false := by
    funext state
    exact LenCallFacts.actual_len_noncapturing options () remaining span limits state
  have canUnwind : h.abiCanUnwind LenHelper.abi = true := LenCallFacts.abi_flags.2.1
  have variadic : h.abiVariadic LenHelper.abi = false := LenCallFacts.abi_flags.1
  have conv : h.sameConvention LenHelper.abi LenHelper.abi = true := by
    change (LenHelper.abi.conv == LenHelper.abi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs LenHelper.abi = LenHelper.abi.args := rfl
  have ret : h.abiReturn LenHelper.abi = LenHelper.abi.ret := rfl
  have get0 : LenHelper.abi.args.getD 0 LenHelper.abi.ret = LenHelper.abi.args[0]'(by rw [LenCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_internal ".Call.require"
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, canUnwind, conv, args,
    LenCallFacts.body_flags.1, LenCallFacts.body_flags.2,
    LenCallFacts.abi_flags.2.2, ret, get0, spanAt, require,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout =>
    cases operand <;> rfl
end DuplicatePrefix.LenCallCore


open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.LenCallCore." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
