import Miri.Memory.Scalar

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def bits (n : Nat) : U128 := BitVec.ofNat 128 n

private def requireError (label : String) (expected : ε) [DecidableEq ε]
    (result : Except ε α) : IO Unit := do
  match result with
  | .error actual =>
    if actual != expected then
      throw (IO.userError s!"{label}: got an unexpected error value")
  | .ok _ => throw (IO.userError s!"{label}: invalid input returned a value")

def main : IO Unit := do
  requireError "zero-sized ScalarInt" ScalarIntError.zeroSize (ScalarInt.null (size 0))
  requireError "oversized ScalarInt" (ScalarIntError.sizeTooLarge (size 17))
    (ScalarInt.tryFromUInt (bits 0) (size 17))
  requireError "integer outside source i128" (ScalarIntError.integerOutsideI128 (2 ^ 127))
    (ScalarInt.truncateFromInt (2 ^ 127) (size 16))
  requireError "ScalarInt width mismatch" (ScalarIntError.sizeMismatch (size 2) (size 1))
    (ScalarInt.trueValue.toBits (size 2))
  requireError "ScalarInt invalid atomic ordering"
    (ScalarIntError.invalidAtomicOrdering 5)
    (do
      let value ← ScalarInt.tryFromUInt (bits 5) (size 4)
      match value with
      | some scalar => scalar.toAtomicOrdering
      | none => throw (ScalarIntError.invalidAtomicOrdering 5))
  requireError "ScalarInt invalid SIMD alignment" (ScalarIntError.invalidSimdAlignment 3)
    (do
      let value ← ScalarInt.tryFromUInt (bits 3) (size 4)
      match value with
      | some scalar => scalar.toSimdAlignment
      | none => throw (ScalarIntError.invalidSimdAlignment 3))

  requireError "Scalar unsigned constructor overflow"
    (ScalarError.scalarInt (.integerConversionOverflow 256))
    (Scalar.fromUInt (bits 256) (size 1) : Except ScalarError (Scalar CtfeProvenance))
  requireError "Scalar signed constructor overflow"
    (ScalarError.scalarInt (.integerConversionOverflow (-129)))
    (Scalar.fromInt (-129) (size 1) : Except ScalarError (Scalar CtfeProvenance))
  let invalidBool : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt8 2)
  requireError "Scalar invalid bool" (ScalarError.scalarInt (.invalidBool 2))
    invalidBool.toBool
  let invalidChar : Scalar CtfeProvenance :=
    Scalar.fromScalarInt (ScalarInt.ofUInt32 ⟨0xd800⟩)
  requireError "Scalar invalid char" (ScalarError.scalarInt (.invalidChar 0xd800))
    invalidChar.toChar
  let twoByte : Scalar CtfeProvenance := Scalar.fromScalarInt (ScalarInt.ofUInt16 1)
  requireError "Scalar size mismatch" (ScalarError.scalarInt (.sizeMismatch (size 1) (size 2)))
    (twoByte.toUInt8)
  requireError "zero-sized Scalar bits" ScalarError.zeroSizedBits
    ((Scalar.fromBool true : Scalar CtfeProvenance).toBits (size 0))
  IO.println "scalar invalid domains rejected explicitly"
