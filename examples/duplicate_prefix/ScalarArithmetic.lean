import Lean
import Miri.Interpreter.IntegerOps

/-! The actual scalar integer operations used by the root's guards. These
lemmas operate on the interpreter's checked ScalarInt/IntegerValue encoding,
rather than replacing the integer evaluator with Nat arithmetic. -/

namespace DuplicatePrefix.ScalarArithmetic
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

def usizeValue (value : UInt64) : IntegerValue :=
  ⟨ScalarInt.ofUInt64 value, ⟨Size.ofBytes 8, .usize⟩⟩

theorem truncate_nat64 (value : Nat) (fits : value < 18446744073709551616) :
    BitVec.setWidth 128 (BitVec.extractLsb 63 0 (BitVec.ofInt 128 (Int.ofNat value))) =
      BitVec.ofNat 128 value := by
  have wide : value < 2 ^ 128 := by omega
  apply BitVec.eq_of_toNat_eq
  simp [-Int.natCast_ediv, BitVec.ofInt_natCast, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt wide]


open Lean Elab Tactic in
elab "simp_scalar_implementation" : tactic => do
  let env ← getEnv
  let suffixes := [".IntegerOps.arithmetic", ".IntegerOps.truncate", ".IntegerOps.scalarResult",
    ".ScalarInt.truncated", ".ScalarInt.checkedWidth", ".Size.integerWidth"]
  let names ← suffixes.mapM fun (suffix : String) => do
    let candidates := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected one source helper {suffix}, found {candidates.length}"
  let names := names.toArray
  evalTactic (← `(tactic| simp [usizeValue, IntegerType.signed, IntegerKind.signed,
    ScalarInt.truncateFromUInt, Size.truncate, Size.bits, Size.ofBytes,
    BinOp.isUnchecked, BinOp.isOverflowing, bind, Except.bind, pure, Except.pure,
    Except.mapError, $[$names:ident],*]))


theorem decode_usize (value : UInt64) :
    IntegerOps.decode (usizeValue value) = .ok (Int.ofNat value.toNat) := by
  have bound : value.toNat < 2 ^ 128 := by
    have smaller : value.toNat < 18446744073709551616 := value.toNat_lt_size
    omega
  simp [IntegerOps.decode, usizeValue, IntegerType.signed, IntegerKind.signed,
    ScalarInt.toUInt, ScalarInt.toBits, ScalarInt.ofUInt64, Size.ofBytes,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, bind, Except.bind,
    pure, Except.pure, Except.mapError]

theorem usize_eq (left right : UInt64) :
    IntegerOps.binary .Eq (usizeValue left) (usizeValue right) =
      .ok (.boolean (left == right)) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp [usizeValue, bind, Except.bind, pure, Except.pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro equality
    apply UInt64.toNat_inj.mp
    exact Int.ofNat.inj equality
  · intro equality
    subst right
    rfl

theorem usize_gt (left right : UInt64) :
    IntegerOps.binary .Gt (usizeValue left) (usizeValue right) =
      .ok (.boolean (left > right)) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp [usizeValue, bind, Except.bind, pure, Except.pure, UInt64.lt_iff_toNat_lt]

theorem truncate_usize_success (value : U128) :
    ∃ scalar overflow, ScalarInt.truncateFromUInt value (Size.ofBytes 8) =
      .ok (scalar, overflow) := by
  exact ⟨_, _, rfl⟩

theorem usize_div_two_success (value : UInt64) :
    ∃ result, IntegerOps.binary .Div (usizeValue value) (usizeValue 2) =
      .ok (.scalar result) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp only [bind, Except.bind]
  simp [usizeValue]
  simp_scalar_implementation

theorem usize_div_two (value : UInt64) :
    IntegerOps.binary .Div (usizeValue value) (usizeValue 2) =
      .ok (.scalar (ScalarInt.ofUInt64 (value / 2))) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp only [bind, Except.bind]
  simp [usizeValue]
  simp_scalar_implementation
  have quotientBound : value.toNat / 2 < 18446744073709551616 := by
    have bound : value.toNat < 18446744073709551616 := value.toNat_lt_size
    omega
  have quotientBound128 : value.toNat / 2 < 2 ^ 128 := by omega
  simp only [ScalarInt.ofUInt64]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (value.toNat : Int) / 2 = Int.ofNat (value.toNat / 2) from rfl]
  simp [-Int.natCast_ediv, BitVec.ofInt_natCast, BitVec.toNat_setWidth,
    UInt64.toNat_div, Nat.mod_eq_of_lt quotientBound,
    Nat.mod_eq_of_lt quotientBound128]

theorem usize_mul_one (value : UInt64) :
    IntegerOps.binary .MulWithOverflow (usizeValue value) (usizeValue 1) =
      .ok (.withOverflow (ScalarInt.ofUInt64 value) false) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp only [bind, Except.bind]
  simp [usizeValue]
  simp_scalar_implementation
  have bound : value.toNat < 18446744073709551616 := value.toNat_lt_size
  have wide : value.toNat < 340282366920938463463374607431768211456 := by omega
  have bits : BitVec.setWidth 128 (BitVec.ofNat 64
      (value.toNat % 340282366920938463463374607431768211456)) =
      BitVec.ofNat 128 value.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt wide]
  simp [bits, ScalarInt.ofUInt64, Size.ofBytes]
  omega

theorem truncate_word (value : UInt64) :
    ScalarInt.truncateFromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 8) =
      .ok (ScalarInt.ofUInt64 value, false) := by
  simp_scalar_implementation
  have bound : value.toNat < 18446744073709551616 := value.toNat_lt_size
  have wide : value.toNat < 340282366920938463463374607431768211456 := by omega
  have bits : BitVec.setWidth 128 (BitVec.ofNat 64
      (value.toNat % 340282366920938463463374607431768211456)) =
      BitVec.ofNat 128 value.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt wide]
  simp [bits, ScalarInt.ofUInt64, Size.ofBytes]

end DuplicatePrefix.ScalarArithmetic
