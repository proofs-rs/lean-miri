import Lean
import Miri.Memory.Pointer
import Miri.Memory.ScalarInt

namespace DuplicatePrefix.PointerArithmetic

open Lean Elab Tactic
open Miri.ABI Miri.Memory

private def target64 : Miri.Memory.PointerArithmetic := ⟨Size.ofBytes 8⟩

private def findUniquePrivate (suffix : String) : TacticM Name := do
  let env ← getEnv
  let candidates := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError m!"expected one private definition `{suffix}`, found {candidates.length}"

elab "simp_pointer_64" : tactic => do
  let helpers ← [
    ".PointerArithmetic.sizeResult",
    ".PointerArithmetic.toUInt64Checked",
    ".Size.integerWidth"
  ].mapM findUniquePrivate
  let helperIds := helpers.toArray.map mkIdent
  let generated ← `(tactic| simp [target64, Miri.Memory.PointerArithmetic.truncateToTargetUsize,
    Miri.ABI.Size.truncate, $[$helperIds:ident],*])
  evalTactic generated

private theorem truncate_size_eight (value : UInt64) :
    (Size.ofBytes 8).truncate (BitVec.ofNat 128 value.toNat) =
      .ok (BitVec.ofNat 128 value.toNat) := by
  have hBits : Size.bits (Size.ofBytes 8) = .ok 64 := by decide
  simp_pointer_64
  rw [hBits]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hval : value.toNat < 2 ^ 64 := UInt64.toNat_lt_size value
  have hmod : value.toNat % 2 ^ 128 = value.toNat := Nat.mod_eq_of_lt (by omega)
  simp
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by omega)]
  simp only [BitVec.toNat_ofNat]
  rw [hmod]
  exact Nat.mod_eq_of_lt hval
#print axioms truncate_size_eight

theorem truncate_u64_identity (value : UInt64) :
    target64.truncateToTargetUsize value = .ok value := by
  unfold target64 Miri.Memory.PointerArithmetic.truncateToTargetUsize
  rw [truncate_size_eight]
  simp_pointer_64
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hval : value.toNat < 2 ^ 64 := UInt64.toNat_lt_size value
  have h128 : value.toNat < 2 ^ 128 := by omega
  simp [Except.mapError, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128, hval, UInt64.ofNat_toNat]

#print axioms truncate_u64_identity

variable {Prov : Type}

theorem wrapping_offset_u64 (ptr : Pointer Prov) (delta : Size) :
    ptr.wrappingOffset delta target64 =
      .ok { ptr with offset := Size.ofBytes (ptr.offset.bytes + delta.bytes) } := by
  unfold Pointer.wrappingOffset
  rw [truncate_u64_identity]
  rfl

#print axioms wrapping_offset_u64

theorem scalar_ofUInt64_toInt_size_eight (value : UInt64)
    (h : value.toNat < 2 ^ 63) :
    (ScalarInt.ofUInt64 value).toInt (Size.ofBytes 8) =
      .ok (Int.ofNat value.toNat) := by
  unfold ScalarInt.toInt ScalarInt.toBits
  simp [ScalarInt.ofUInt64]
  have hBits : Size.bits (Size.ofBytes 8) = .ok 64 := by decide
  unfold Size.signExtend
  simp_pointer_64
  rw [hBits]
  simp only [Bind.bind, Except.bind]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp
  have h128 : value.toNat < 2 ^ 128 := by omega
  rw [BitVec.toInt_signExtend_of_le (by omega)]
  rw [BitVec.toInt_eq_toNat_of_lt]
  · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128,
      Nat.mod_eq_of_lt (show value.toNat < 2 ^ 64 by omega), Except.mapError]
  · simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128,
      Nat.mod_eq_of_lt (show value.toNat < 2 ^ 64 by omega)]
    omega

#print axioms scalar_ofUInt64_toInt_size_eight

theorem scalar_ofUInt64_toTargetIsize_size_eight (value : UInt64)
    (h : value.toNat < 2 ^ 63) :
    (ScalarInt.ofUInt64 value).toTargetIsize (Size.ofBytes 8) =
      .ok (Int64.ofInt (Int.ofNat value.toNat)) := by
  unfold ScalarInt.toTargetIsize
  rw [scalar_ofUInt64_toInt_size_eight value h]
  have hInt : (Int.ofNat value.toNat) < (2 ^ 63 : Int) := Int.ofNat_lt.mpr h
  have hguard : ¬ (Int.ofNat value.toNat < -(2 ^ 63 : Int) ∨
      (2 ^ 63 : Int) ≤ Int.ofNat value.toNat) := by
    apply not_or.mpr
    constructor
    · apply Int.not_lt_of_ge
      exact Int.le_trans ((Int.neg_nonpos_iff _).mpr (Int.natCast_nonneg _))
        (Int.ofNat_nonneg _)
    · exact Int.not_le.mpr hInt
  have hlow : ¬ (Int.ofNat value.toNat < -(2 ^ 63 : Int)) := hguard ∘ Or.inl
  have hhigh : ¬ ((2 ^ 63 : Int) ≤ Int.ofNat value.toNat) := hguard ∘ Or.inr
  simp only [Bind.bind, Except.bind]
  have hbool : (decide (Int.ofNat value.toNat < -(2 ^ 63 : Int)) ||
      decide (Int.ofNat value.toNat ≥ (2 ^ 63 : Int))) = false := by
    apply Bool.or_eq_false_iff.mpr
    constructor
    · exact (decide_eq_false_iff_not).2 hlow
    · exact (decide_eq_false_iff_not).2 hhigh
  rw [hbool]
  rfl

#print axioms scalar_ofUInt64_toTargetIsize_size_eight

end DuplicatePrefix.PointerArithmetic
