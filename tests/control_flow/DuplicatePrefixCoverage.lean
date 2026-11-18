import Miri.Input.Decoder
import Miri.Verification.StepWP
import MiriTests.ControlFlow.Transitions
/-! Validate the opcode inventory of the retained duplicate_prefix MIR export.
Run `lake env lean --run tests/control_flow/DuplicatePrefixCoverage.lean INPUT.json`.
The test decodes real MIR and checks block lowering and rule coverage. -/

open Miri.MIR Miri.Input Miri.Verification.StepWP

def projectionOK : ProjectionElem → Bool
  | .Deref | .Downcast .. | .Field .. => true
  | _ => false
def placeOK (p : Place) : Bool := p.projection.all projectionOK
def operandOK : Operand → Bool
  | .Copy p | .Move p => placeOK p
  | .Constant .. | .RuntimeChecks .. => true
def rvalueOK : Rvalue → Bool
  | .Use x _ => operandOK x
  | .Ref _ _ p | .RawPtr _ p | .Discriminant p => placeOK p
  | .Cast kind x _ =>
    (match kind with | .IntToInt | .PtrToPtr | .Transmute => true | _ => false) && operandOK x
  | .Aggregate kind xs =>
    (match kind with | .Tuple | .Adt .. => true | _ => false) && xs.all operandOK
  | .UnaryOp kind x =>
    (match kind with | .Not | .PtrMetadata => true | _ => false) && operandOK x
  | .BinaryOp kind x y =>
    (match kind with
     | .BitAnd | .BitOr | .Div | .Eq | .Ge | .Gt | .Lt | .MulWithOverflow
     | .Offset | .Shl | .Sub | .SubWithOverflow => true
     | _ => false) && operandOK x && operandOK y
  | _ => false
def statementOK : StatementKind → Bool
  | .Assign p rhs => placeOK p && rvalueOK rhs
  | .StorageLive _ | .StorageDead _ => true
  | .PlaceMention p => placeOK p
  | .Intrinsic (.CopyNonOverlapping args) =>
    operandOK args.source && operandOK args.destination && operandOK args.count
  | _ => false
def termOK : TerminatorKind → Bool
  | .Goto .. | .Return => true
  | .SwitchInt x _ => operandOK x
  | .Call x args dest .. => operandOK x && args.all (operandOK ∘ SpannedOperand.operand) && placeOK dest
  | .Drop p .. => placeOK p
  | .Assert x _ message .. =>
    operandOK x && (match message with
      | .DivisionByZero y => operandOK y
      | .Overflow op l r => rvalueOK (.BinaryOp op l r)
      | _ => false)
  | _ => false

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected input path")
  let .ok input ← decodeFile path | throw (IO.userError "could not decode MIR")
  let mut blocks := 0
  let mut statements := 0
  for body in input.document.bodies do
    for block in body.mir.basicBlocks do
      blocks := blocks + 1
      unless (lowerBlock (hooks := ControlTests.stepHooks) (allowed := fun _ _ => True) block).isSome do
        throw (IO.userError s!"block did not lower: {repr block.terminator.kind}")
      unless termOK block.terminator.kind do
        throw (IO.userError s!"uncovered terminator: {repr block.terminator.kind}")
      for statement in block.statements do
        statements := statements + 1
        unless statementOK statement.kind do
          throw (IO.userError s!"uncovered statement: {repr statement.kind}")
  IO.println s!"Checked {input.document.bodies.size} MIR bodies, {blocks} blocks and {statements} statements"
