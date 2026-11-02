import duplicate_prefix.PointerArithmetic
import Miri.Memory.Scalar

/-! Pointer/scalar encoding facts used by the actual pointer-add dispatch. -/

namespace DuplicatePrefix.ScalarPointers
open Miri.ABI Miri.Memory

theorem pointer_roundtrip [PointerProvenance Prov]
    (target : TargetDataLayout) (pointer : Pointer Prov) :
    (Scalar.fromPointer target pointer).toPointer target = .ok pointer.withOptionalProvenance := by
  simp [Scalar.toPointer, Scalar.toBitsOrPtrInternal, Scalar.fromPointer,
    bind, Except.bind, pure, Except.pure]

theorem from_some_pointer (target : TargetDataLayout) (pointer : Pointer Prov) :
    Scalar.fromMaybePointer target pointer.withOptionalProvenance =
      .ok (Scalar.fromPointer target pointer) := by rfl

theorem scalar_int_one :
    Scalar.fromInt (Prov := Prov) 1 (Size.ofBytes 8) =
      .ok (Scalar.fromScalarInt (ScalarInt.ofUInt64 1)) := by rfl

theorem scalar_false_bool [PointerProvenance Prov] :
    (Scalar.fromBool (Prov := Prov) false).toBool = .ok false := by rfl

theorem scalar_uint64_to_int [PointerProvenance Prov] (value : UInt64)
    (fits : value.toNat < 2 ^ 63) :
    (Scalar.fromScalarInt (Prov := Prov) (ScalarInt.ofUInt64 value)).toInt (Size.ofBytes 8) =
      .ok (Int.ofNat value.toNat) := by
  have signed := PointerArithmetic.scalar_ofUInt64_toInt_size_eight value fits
  unfold ScalarInt.toInt at signed
  simp [ScalarInt.toBits, ScalarInt.ofUInt64, bind, Except.bind,
    pure, Except.pure] at signed
  simp [Scalar.toInt, Scalar.toBits, Scalar.toScalarInt, Scalar.tryToScalarInt,
    Scalar.fromScalarInt, ScalarInt.toBits, ScalarInt.ofUInt64, Size.ofBytes,
    bind, Except.bind, pure, Except.pure, Except.mapError] at signed ⊢
  cases result : ({bytes := 8} : Size).signExtend (BitVec.ofNat 128 value.toNat) with
  | error error => simp [result] at signed
  | ok resultValue => simpa [result] using signed

theorem scalar_uint64_to_isize [PointerProvenance Prov] (value : UInt64)
    (fits : value.toNat < 2 ^ 63) :
    (Scalar.fromScalarInt (Prov := Prov) (ScalarInt.ofUInt64 value)).toTargetIsize (Size.ofBytes 8) =
      .ok (Int64.ofInt (Int.ofNat value.toNat)) := by
  unfold Scalar.toTargetIsize
  rw [scalar_uint64_to_int value fits]
  simp [bind, Except.bind, pure, Except.pure]
  omega

end DuplicatePrefix.ScalarPointers
