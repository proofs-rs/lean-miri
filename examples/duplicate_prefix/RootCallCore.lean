import duplicate_prefix.RootArgumentEntry

/-! Exact source reduction of root initStackFrame to its two ordinary argument
initializations. The actual compiler queries are discharged; destination
protection, retag scope, all argument/count checks and full-stop cleanup remain. -/
namespace DuplicatePrefix.RootCallCore
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

noncomputable def argumentBody (h : RootHooks) (first second : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  spanAt h (← h.localSpan RootBody.reflected.body.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy first) (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
    (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret) 0 ⟨1, #[]⟩ ty.ty false
  spanAt h (← h.localSpan RootBody.reflected.body.body 2)
  let ty ← h.localLayout () 2
  Call.passArgument h () (.Copy second) (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret)
    (RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret) 1 ⟨2, #[]⟩ ty.ty false
  pure (2, 2)

noncomputable def core (h : RootHooks) (first second : OpTy Provenance) (destination : MPlaceTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  h.pushRaw () RootBody.reflected.functionInstance RootBody.reflected.body (.memory destination) (.stop true)
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (argumentBody h first second)
  spanAt h (← h.localSpan RootBody.reflected.body.body 0)
  unless ← h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  h.protectArgument () destination
  spanAt h preamble
  require (calleeIndex == RootCompilerFacts.rootAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 2 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first second : OpTy Provenance) (destination : MPlaceTy Provenance) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy first, .Copy second] false (.memory destination) (.stop true) =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first second destination := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation RootBody.reflected.functionInstance = pure false := by
    funext state
    exact CallEntryFacts.actual_call_hooks_requires_no_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () RootBody.reflected.functionInstance #[] = pure RootCompilerFacts.rootAbi := by
    funext state
    exact CallEntryFacts.actual_call_hooks_root_abi options () remaining span limits state
  have features : h.checkTargetFeatures () RootBody.reflected.functionInstance = pure () := by
    funext state
    exact CallEntryFacts.actual_call_hooks_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () RootBody.reflected.functionInstance RootCompilerFacts.rootAbi = pure false := by
    funext state
    exact CallEntryFacts.actual_call_hooks_non_capturing_false options () remaining span limits state
  have memory : h.placeToOp () (.memory destination) = pure ⟨.indirect destination.mplace, destination.layout⟩ := by
    funext state
    exact CallEntryLocals.destination_memory options limits remaining span destination state
  have variadic : h.abiVariadic RootCompilerFacts.rootAbi = false := CallEntryFacts.root_abi_entry_flags.1
  have conv : h.sameConvention RootCompilerFacts.rootAbi RootCompilerFacts.rootAbi = true := by
    change (RootCompilerFacts.rootAbi.conv == RootCompilerFacts.rootAbi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs RootCompilerFacts.rootAbi = RootCompilerFacts.rootAbi.args := rfl
  have ret : h.abiReturn RootCompilerFacts.rootAbi = RootCompilerFacts.rootAbi.ret := rfl
  have get0 : RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret = RootCompilerFacts.rootAbi.args[0]'(by rw [CallEntryFacts.root_abi_entry_flags.2.2.1]; decide) := by with_unfolding_all rfl
  have get1 : RootCompilerFacts.rootAbi.args.getD 1 RootCompilerFacts.rootAbi.ret = RootCompilerFacts.rootAbi.args[1]'(by rw [CallEntryFacts.root_abi_entry_flags.2.2.1]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first second destination
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_internal ".Call.require"
  unfold_internal ".Call.at?"
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, memory, closure, variadic, conv, args,
    CallEntryFacts.root_body_entry_flags.1, CallEntryFacts.root_body_entry_flags.2,
    CallEntryFacts.root_abi_entry_flags.2.2.1, ret, get0, get1, spanAt, require, argumentBody,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
end DuplicatePrefix.RootCallCore

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootCallCore.actual_entry_eq) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root entry reduction dependency {dependency}"
