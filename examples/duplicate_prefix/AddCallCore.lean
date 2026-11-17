import duplicate_prefix.AddCallFacts
import duplicate_prefix.RootCallCore

/-! Source initStackFrame for the three ordinary copy arguments and the
implicit caller-location argument. -/
namespace DuplicatePrefix.AddCallCore
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

noncomputable def checkedAt {α : Type} (values : Array α) (index : Nat) (message : String) :
    MachineHooks.M MiriMemoryKind Machine.RootUser α :=
  match values[index]? with
  | none => throw (.invalidProgram message)
  | some value => pure value
noncomputable def implicitAbi (index : Nat) :=
  checkedAt HelperCompilerFacts.addAbi.args index "missing implicit caller location ABI"

noncomputable def core (h : RootHooks) (first second : OpTy Provenance) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let callerLocation ← h.callerLocation
  let destinationOp ← h.placeToOp () destination
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  h.pushRaw () HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody destination cont
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := some callerLocation}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry do
    spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 1)
    let ty ← h.localLayout () 1
    Call.passArgument h () (.Copy first) (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret) 0 ⟨1, #[]⟩ ty.ty false
    spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 2)
    let ty ← h.localLayout () 2
    Call.passArgument h () (.Copy second) (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret)
      (HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret) 1 ⟨2, #[]⟩ ty.ty false
    pure (2, 2)
  spanAt h (← h.localSpan HelperCompilerFacts.addBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.addAbi.ret HelperCompilerFacts.addAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  let _ ← implicitAbi calleeIndex
  require (calleeIndex+1 == HelperCompilerFacts.addAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 2 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

open Lean Elab Tactic in
elab "fold_add_implicit_source" : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".Call.at?" then some (mkIdent name) else none
  let atName ← match found with
    | [name] => pure name
    | _ => throwError "expected private Call.at?"
  let lemmaName := mkIdent `source_at_same
  evalTactic (← `(tactic|
    have $lemmaName:ident {α : Type} (values : Array α) (index : Nat) (message : String) :
        ($atName:ident values index message : MachineHooks.M MiriMemoryKind Machine.RootUser α) =
          checkedAt values index message := by
      funext state
      unfold $atName:ident checkedAt
      cases same : (values[index]?) <;> rfl))
  evalTactic (← `(tactic| simp only [$lemmaName:ident]))


theorem actual_entry_eq (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (first second : OpTy Provenance) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      HelperCompilerFacts.addCall.callee HelperCompilerFacts.addBody HelperCompilerFacts.addAbi
      #[.Copy first,.Copy second] true destination cont =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first second destination cont := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation HelperCompilerFacts.addCall.callee = pure true := by
    funext state
    exact AddCallFacts.actual_add_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () HelperCompilerFacts.addCall.callee #[] = pure HelperCompilerFacts.addAbi := by
    funext state
    exact AddCallFacts.actual_add_abi options () remaining span state
  have features : h.checkTargetFeatures () HelperCompilerFacts.addCall.callee = pure () := by
    funext state
    exact AddCallFacts.actual_add_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () HelperCompilerFacts.addCall.callee HelperCompilerFacts.addAbi = pure false := by
    funext state
    exact AddCallFacts.actual_add_noncapturing options () remaining span limits state
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.addAbi = true := AddCallFacts.abi_flags.2.1
  have variadic : h.abiVariadic HelperCompilerFacts.addAbi = false := AddCallFacts.abi_flags.1
  have conv : h.sameConvention HelperCompilerFacts.addAbi HelperCompilerFacts.addAbi = true := by
    change (HelperCompilerFacts.addAbi.conv == HelperCompilerFacts.addAbi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs HelperCompilerFacts.addAbi = HelperCompilerFacts.addAbi.args := rfl
  have ret : h.abiReturn HelperCompilerFacts.addAbi = HelperCompilerFacts.addAbi.ret := rfl
  have get0 : HelperCompilerFacts.addAbi.args.getD 0 HelperCompilerFacts.addAbi.ret = HelperCompilerFacts.addAbi.args[0]'(by rw [AddCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  have get1 : HelperCompilerFacts.addAbi.args.getD 1 HelperCompilerFacts.addAbi.ret = HelperCompilerFacts.addAbi.args[1]'(by rw [AddCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  have get2 : HelperCompilerFacts.addAbi.args.getD 2 HelperCompilerFacts.addAbi.ret = HelperCompilerFacts.addAbi.args[2]'(by rw [AddCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first second destination cont
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core
  unfold_internal ".Call.require"
  fold_add_implicit_source
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, canUnwind, conv, args,
    AddCallFacts.body_flags.1, AddCallFacts.body_flags.2,
    AddCallFacts.abi_flags.2.2, ret, get0, get1, get2, spanAt, require, checkedAt, implicitAbi,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
  funext callerLocation
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout =>
    cases operand <;> simp only [map_eq_pure_bind,bind_assoc] <;> rfl
end DuplicatePrefix.AddCallCore


open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AddCallCore." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
