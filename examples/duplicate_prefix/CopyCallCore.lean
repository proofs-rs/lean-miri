import duplicate_prefix.CopyCallFacts
import duplicate_prefix.RootCallCore

/-! Source initStackFrame for the three ordinary copy arguments and the
implicit caller-location argument. -/
namespace DuplicatePrefix.CopyCallCore
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
  checkedAt HelperCompilerFacts.copyAbi.args index "missing implicit caller location ABI"

noncomputable def argumentBody (h : RootHooks) (first second third : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser (Nat × Nat) := do
  spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 1)
  let ty ← h.localLayout () 1
  Call.passArgument h () (.Copy first) (HelperCompilerFacts.copyAbi.args.getD 0 HelperCompilerFacts.copyAbi.ret)
    (HelperCompilerFacts.copyAbi.args.getD 0 HelperCompilerFacts.copyAbi.ret) 0 ⟨1, #[]⟩ ty.ty false
  spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 2)
  let ty ← h.localLayout () 2
  Call.passArgument h () (.Copy second) (HelperCompilerFacts.copyAbi.args.getD 1 HelperCompilerFacts.copyAbi.ret)
    (HelperCompilerFacts.copyAbi.args.getD 1 HelperCompilerFacts.copyAbi.ret) 1 ⟨2, #[]⟩ ty.ty false
  spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 3)
  let ty ← h.localLayout () 3
  Call.passArgument h () (.Copy third) (HelperCompilerFacts.copyAbi.args.getD 2 HelperCompilerFacts.copyAbi.ret)
    (HelperCompilerFacts.copyAbi.args.getD 2 HelperCompilerFacts.copyAbi.ret) 2 ⟨3, #[]⟩ ty.ty false
  pure (3, 3)

noncomputable def core (h : RootHooks) (first second third : OpTy Provenance) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let callerLocation ← h.callerLocation
  let destinationOp ← h.placeToOp () destination
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  h.pushRaw () HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyBody destination cont
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := some callerLocation}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (argumentBody h first second third)
  spanAt h (← h.localSpan HelperCompilerFacts.copyBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.copyAbi.ret HelperCompilerFacts.copyAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  let _ ← implicitAbi calleeIndex
  require (calleeIndex+1 == HelperCompilerFacts.copyAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 3 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

open Lean Elab Tactic in
elab "fold_copy_implicit_source" : tactic => do
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
    (first second third : OpTy Provenance) (destination : RuntimeStackPlace Provenance) (cont : ReturnContinuation) :
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) ()
      HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyBody HelperCompilerFacts.copyAbi
      #[.Copy first,.Copy second,.Copy third] true destination cont =
    core (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits) first second third destination cont := by
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits
  have requires : h.requiresCallerLocation HelperCompilerFacts.copyCall.callee = pure true := by
    funext state
    exact CopyCallFacts.actual_copy_caller_location options () remaining span limits state
  have abi : h.fnAbiOfInstance () HelperCompilerFacts.copyCall.callee #[] = pure HelperCompilerFacts.copyAbi := by
    funext state
    exact CopyCallFacts.actual_copy_abi options () remaining span state
  have features : h.checkTargetFeatures () HelperCompilerFacts.copyCall.callee = pure () := by
    funext state
    exact CopyCallFacts.actual_copy_target_features options () remaining span limits state
  have closure : h.nonCapturingClosure () HelperCompilerFacts.copyCall.callee HelperCompilerFacts.copyAbi = pure false := by
    funext state
    exact CopyCallFacts.actual_copy_noncapturing options () remaining span limits state
  have canUnwind : h.abiCanUnwind HelperCompilerFacts.copyAbi = true := CopyCallFacts.abi_flags.2.1
  have variadic : h.abiVariadic HelperCompilerFacts.copyAbi = false := CopyCallFacts.abi_flags.1
  have conv : h.sameConvention HelperCompilerFacts.copyAbi HelperCompilerFacts.copyAbi = true := by
    change (HelperCompilerFacts.copyAbi.conv == HelperCompilerFacts.copyAbi.conv) = true
    exact beq_self_eq_true _
  have args : h.abiArgs HelperCompilerFacts.copyAbi = HelperCompilerFacts.copyAbi.args := rfl
  have ret : h.abiReturn HelperCompilerFacts.copyAbi = HelperCompilerFacts.copyAbi.ret := rfl
  have get0 : HelperCompilerFacts.copyAbi.args.getD 0 HelperCompilerFacts.copyAbi.ret = HelperCompilerFacts.copyAbi.args[0]'(by rw [CopyCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  have get1 : HelperCompilerFacts.copyAbi.args.getD 1 HelperCompilerFacts.copyAbi.ret = HelperCompilerFacts.copyAbi.args[1]'(by rw [CopyCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  have get2 : HelperCompilerFacts.copyAbi.args.getD 2 HelperCompilerFacts.copyAbi.ret = HelperCompilerFacts.copyAbi.args[2]'(by rw [CopyCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  have get3 : HelperCompilerFacts.copyAbi.args.getD 3 HelperCompilerFacts.copyAbi.ret = HelperCompilerFacts.copyAbi.args[3]'(by rw [CopyCallFacts.abi_flags.2.2]; decide) := by with_unfolding_all rfl
  change Call.initStackFrame h () _ _ _ _ _ _ _ = core h first second third destination cont
  generalize hDef : h = hooks at *
  unfold Call.initStackFrame core argumentBody
  unfold_internal ".Call.require"
  fold_copy_implicit_source
  unfold_internal ".Call.setSpan"
  simp [requires, abi, features, closure, variadic, canUnwind, conv, args,
    CopyCallFacts.body_flags.1, CopyCallFacts.body_flags.2,
    CopyCallFacts.abi_flags.2.2, ret, get0, get1, get2, get3, spanAt, require, checkedAt, implicitAbi,
    List.range'_succ, List.forIn_cons, List.forIn_nil, bind_assoc]
  congr 1
  funext callerLocation
  congr 1
  funext destinationOp
  cases destinationOp with
  | mk operand layout =>
    cases operand <;> simp only [map_eq_pure_bind,bind_assoc] <;> rfl
end DuplicatePrefix.CopyCallCore


open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CopyCallCore." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved metadata call dependency {dependency}"
