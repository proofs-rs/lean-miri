import Miri.Interpreter.IntegerOps

open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def flag (value : Bool) : Nat := if value then 1 else 0

def integerKind (size : Nat) (signed : Bool) : IntegerKind :=
  match size, signed with
  | 1, true => .i8 | 2, true => .i16 | 4, true => .i32 | 8, true => .i64
  | 1, false => .u8 | 2, false => .u16 | 4, false => .u32 | 8, false => .u64
  | _, true => .i128 | _, false => .u128

def operand (raw size : Nat) (signed : Bool) : Except IntegerOpError IntegerValue := do
  let (scalar, _) ← ScalarInt.truncateFromUInt (BitVec.ofNat 128 raw) (Size.ofBytes (UInt64.ofNat size))
    |>.mapError .scalar
  return ⟨scalar, ⟨Size.ofBytes (UInt64.ofNat size), integerKind size signed⟩⟩

def showResult : Except IntegerOpError IntegerResult → String
  | .ok (.scalar value) => s!"S{value.data.toNat}"
  | .ok (.withOverflow value overflow) => s!"P{value.data.toNat}:{flag overflow}"
  | .ok (.boolean value) => s!"B{flag value}"
  | .ok (.ordering value) => "O" ++ match value with
      | .lt => "-1" | .eq => "0" | .gt => "1"
  | .error (.undefinedBehavior reason) => "E" ++ match reason with
      | .divisionByZero => "DivisionByZero"
      | .remainderByZero => "RemainderByZero"
      | .divisionOverflow => "DivisionOverflow"
      | .remainderOverflow => "RemainderOverflow"
      | .arithmeticOverflow _ => "ArithOverflow"
      | .shiftOverflow .. => "ShiftOverflow"
  | .error (.asymmetricTypes ..) => "EAsymmetricTypes"
  | .error (.invalidBinaryOperator _) => "EInvalidBinaryOperator"
  | .error error => s!"INTERNAL:{repr error}"

def evaluate (op : BinOp) (l lsize : Nat) (lsigned : Bool)
    (r rsize : Nat) (rsigned : Bool) : String :=
  showResult do
    IntegerOps.binary op (← operand l lsize lsigned) (← operand r rsize rsigned)

def opName (op : BinOp) : String := (repr op).pretty |>.replace "Miri.MIR.BinOp." ""

def main : IO Unit := do
  for size in [1, 2, 4, 8, 16] do
    let bits := size * 8
    let mask := 2 ^ bits - 1
    let values := [0, 1, 2, 2 ^ (bits - 1) - 1, 2 ^ (bits - 1), mask - 1, mask]
    for signed in [false, true] do
      for l in values do
        for r in values do
          for op in [BinOp.Add, .AddUnchecked, .AddWithOverflow,
            .Sub, .SubUnchecked, .SubWithOverflow, .Mul, .MulUnchecked, .MulWithOverflow,
            .Div, .Rem, .BitXor, .BitAnd, .BitOr, .Eq, .Lt, .Le, .Ne, .Ge, .Gt, .Cmp] do
            IO.println s!"{size} {flag signed} {l} {r} {opName op} {evaluate op l size signed r size signed}"
      for rsize in [1, 2, 16] do
        for rsigned in [false, true] do
          for l in values do
            for r in [0, 1, bits - 1, bits, bits + 1, 255, 65535] do
              for op in [BinOp.Shl, .ShlUnchecked, .Shr, .ShrUnchecked] do
                IO.println s!"H{size} {flag signed} {l} {rsize} {flag rsigned} {r} {opName op} {evaluate op l size signed r rsize rsigned}"
  for op in [BinOp.Add, .Shl] do
    let result := do
      let left ← operand 1 8 false
      let right ← operand 2 8 false
      IntegerOps.binary op { left with type := { left.type with kind := .usize } } right
    IO.println s!"CROSS {opName op} {showResult result}"
  let allOps := [BinOp.Add, .AddUnchecked, .AddWithOverflow,
    .Sub, .SubUnchecked, .SubWithOverflow, .Mul, .MulUnchecked, .MulWithOverflow,
    .Div, .Rem, .BitXor, .BitAnd, .BitOr, .Shl, .ShlUnchecked, .Shr, .ShrUnchecked,
    .Eq, .Lt, .Le, .Ne, .Ge, .Gt, .Cmp, .Offset]
  for l in [false, true] do
    for r in [false, true] do
      for op in allOps do
        IO.println s!"B {flag l} {flag r} {opName op} {showResult (IntegerOps.binaryBool op l r)}"
  for leftCode in [0, 97, 55295, 57344, 1114111] do
    for rightCode in [0, 97, 55295, 57344, 1114111] do
      let l := Char.ofNat leftCode
      let r := Char.ofNat rightCode
      for op in allOps do
        IO.println s!"C {l.toNat} {r.toNat} {opName op} {showResult (IntegerOps.binaryChar op l r)}"
