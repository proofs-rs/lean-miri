import duplicate_prefix.SourceControl
import duplicate_prefix.ScalarOperations

namespace DuplicatePrefix.BoolSwitch
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Lean Elab Tactic in
elab "simp_switch_comparison" : tactic => do
  let env ← getEnv
  let names ← ([".ExecutionMachine.lift", ".ExecutionMachine.scalar"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [MachineHooks.run, Call.run,
    ScalarOperations.boolImmediate, Immediate.toScalar,
    ScalarOperations.bool_scalar_roundtrip, bind, EStateM.bind, pure, EStateM.pure,
    Except.bind, Except.pure, Except.mapError, $[$names:ident],*]))

/-- Source switch dispatch composition; the operand-read equation is discharged
by the local read stage when connecting a concrete MIR block. -/
theorem dispatch [DecidableEq K]
    (config : ExecutionMachine.Config K User Choice Other Extern Host)
    (limits : ExecutionMachine.Limits) (choice : Choice)
    (terminator : Terminator) (discriminant : Miri.MIR.Operand)
    (matched otherwise : BasicBlockId)
    (before evaluated : MachineHooks.State K User)
    (layout : LocalLayout) (value : Bool)
    (kind : terminator.kind = .SwitchInt discriminant ⟨#[.Case 0 matched],otherwise⟩)
    (read : MachineHooks.run (do
      PlaceMachine.readImmediate (ExecutionMachine.withValidation config limits).access
        (← OperandMachine.evalOperandAt
          (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)) choice
          (OperandPath.instruction "discriminant") discriminant none)) before =
          (evaluated,.ok (ScalarOperations.boolImmediate value layout)))
    (classification : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).classify
      choice layout.ty = pure .boolean)
    (resultLayout : (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits)).boolLayout
      choice = pure layout)
    (size : layout.layout.size = Size.ofBytes 1) :
    (ExecutionMachine.stepHooks config limits).terminator choice terminator before =
      ControlFlow.goToBlock (if value == false then matched else otherwise) evaluated := by
  change ControlFlow.evalTerminator _ choice terminator before = _
  apply SourceControl.switch_one _ choice terminator discriminant 0 matched otherwise
    before evaluated evaluated (ScalarOperations.boolImmediate value layout) (value == false) kind read
  have zero : Scalar.fromUInt (Prov := Provenance) (BitVec.ofNat 128 0) layout.layout.size =
      .ok (Scalar.fromBool false) := by rw [size]; rfl
  have equality := ScalarOperations.bool_eq
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation config limits))
    choice layout value false classification resultLayout
  simp_switch_comparison

#print axioms dispatch
end DuplicatePrefix.BoolSwitch
