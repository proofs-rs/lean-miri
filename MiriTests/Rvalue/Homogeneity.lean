import Miri.MIR.Operators
open Miri.MIR

def main : IO Unit := do
  let ops : List BinOp := [.Add, .AddUnchecked, .AddWithOverflow, .Sub, .SubUnchecked,
    .SubWithOverflow, .Mul, .MulUnchecked, .MulWithOverflow, .Div, .Rem, .BitXor,
    .BitAnd, .BitOr, .Shl, .ShlUnchecked, .Shr, .ShrUnchecked, .Eq, .Lt, .Le,
    .Ne, .Ge, .Gt, .Cmp, .Offset]
  for op in ops do
    IO.println s!"{op.leftHomogeneous},{op.rightHomogeneous}"
  for op in [UnOp.Not, .Neg, .PtrMetadata] do IO.println s!"{op.homogeneous}"
