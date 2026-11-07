import Miri.Interpreter.OperandMachine
import Miri.MIR.SyntaxTables

namespace Miri.Interpreter.OperandTable
open Miri.ABI Miri.Memory
open MachineHooks (M State)

private def entry (table : MIR.SharedTable α) (id : Nat) (kind : String) : M K U α := do
  match table.lookup id with
  | .ok value => pure value
  | .error _ => throw (.invalidProgram s!"invalid MIR {kind} ID {id}")

def place (tables : MIR.SyntaxTables) (hooks : OperandMachine.Hooks K U C)
    (checkType : C → MIR.PlaceId → OpTy Provenance → M K U Unit)
    (choice : C) (id : MIR.PlaceId) (known : Option LocalLayout) : M K U (OpTy Provenance) := do
  let node ← entry tables.places id.index "place"
  let projections ← entry tables.projectionLists node.projection.index "projection list"
  let mut value ← OperandMachine.localToOp hooks choice node.localId (if projections.isEmpty then known else none)
  for projection in projections do
    value ← OperandMachine.project hooks choice value (← entry tables.projections projection.index "projection")
  checkType choice id value
  return value

def eval (tables : MIR.SyntaxTables) (hooks : OperandMachine.Hooks K U C)
    (checkType : C → MIR.PlaceId → OpTy Provenance → M K U Unit)
    (choice : C) (id : MIR.OperandId) (known : Option LocalLayout)
    (path : Option OperandPath := none) : M K U (OpTy Provenance) := do
  match ← entry tables.operands id.index "operand" with
  | .Copy id | .Move id => place tables hooks checkType choice id known
  | .Constant id =>
    let value ← entry tables.constants id.index "constant"
    match path with
    | none => hooks.constant choice id value.operand known
    | some path => hooks.constantAt choice (path.push (.field "constant")) id value.operand known
  | .RuntimeChecks checks =>
    let value ← hooks.runtimeChecks choice checks
    let layout ← hooks.boolLayout choice
    return ⟨.immediate (.scalar (.fromBool value)),layout⟩

def evalPlaceToOp (hooks : OperandMachine.Hooks K U C) (choice : C)
    (id : MIR.PlaceId) (known : Option LocalLayout) : M K U (OpTy Provenance) := do
  let frame ← MachineHooks.currentFrame
  place frame.mirTables hooks (fun c id value => hooks.checkPlaceType c id value.layout) choice id known

def evalOperand (hooks : OperandMachine.Hooks K U C) (choice : C)
    (id : MIR.OperandId) (known : Option LocalLayout) : M K U (OpTy Provenance) := do
  let frame ← MachineHooks.currentFrame
  eval frame.mirTables hooks (fun c id value => hooks.checkPlaceType c id value.layout) choice id known

def evalOperandAt (hooks : OperandMachine.Hooks K U C) (choice : C) (path : OperandPath)
    (id : MIR.OperandId) (known : Option LocalLayout) : M K U (OpTy Provenance) := do
  let frame ← MachineHooks.currentFrame
  eval frame.mirTables hooks (fun c id value => hooks.checkPlaceType c id value.layout) choice id known path

theorem eval_invalid_operand (tables : MIR.SyntaxTables) (hooks : OperandMachine.Hooks K U C)
    (checkType : C → MIR.PlaceId → OpTy Provenance → M K U Unit)
    (choice : C) (id : MIR.OperandId) (known : Option LocalLayout) (path : Option OperandPath)
    (absent : tables.operands.lookup id.index = .error id.index) :
    eval tables hooks checkType choice id known path =
      (throw (.invalidProgram s!"invalid MIR operand ID {id.index}") : M K U (OpTy Provenance)) := by
  simp only [eval, entry, absent]
  rfl

/-- Checked syntax references select the existing constant callback unchanged. -/
theorem eval_constant {K U C : Type} (tables : MIR.SyntaxTables)
    (hooks : OperandMachine.Hooks K U C)
    (checkType : C → MIR.PlaceId → OpTy Provenance → M K U Unit)
    (choice : C) (id : MIR.OperandId) (constantId : MIR.ConstantId) (node : MIR.ConstantNode)
    (known : Option LocalLayout) (path : Option OperandPath)
    (selected : tables.operands.lookup id.index = .ok (.Constant constantId))
    (constant : tables.constants.lookup constantId.index = .ok node) :
    eval tables hooks checkType choice id known path =
      match path with
      | none => hooks.constant choice constantId node.operand known
      | some path => hooks.constantAt choice (path.push (.field "constant")) constantId node.operand known := by
  simp [eval, entry, selected, constant]

end Miri.Interpreter.OperandTable
