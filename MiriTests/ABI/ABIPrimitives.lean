import Miri.ABI

open Miri.ABI

/-! Finite boundary checks against the pinned rustc_abi Size/Align/
WrappingRange source. These are executable Lean reductions and theorem proofs. -/

example : (Size.fromBits 1).bytes = 1 := by decide
example : (Size.fromBits 9).bytes = 2 := by decide
example : (Size.fromBits 18446744073709551615).bytes = 2305843009213693952 := by decide

example : Size.bits (Size.ofBytes 2305843009213693951) = .ok 18446744073709551608 := by decide
example : Size.bits (Size.ofBytes 2305843009213693952) =
    .error (.bitCountOverflow 2305843009213693952) := by decide
example : Size.bits (Size.ofBytes 18446744073709551615) =
    .error (.bitCountOverflow 18446744073709551615) := by decide

example : Size.add (Size.ofBytes 18446744073709551615) (Size.ofBytes 1) =
    .error (.u64Overflow "add" 18446744073709551615 1) := by decide
example : Size.sub (Size.ofBytes 0) (Size.ofBytes 1) =
    .error (.negativeSubtraction 0 1) := by decide
example : Size.mul (Size.ofBytes 18446744073709551615) 2 =
    .error (.u64Overflow "mul" 18446744073709551615 2) := by decide

example : Size.checkedAdd (Size.ofBytes 32767) (Size.ofBytes 0)
    ({ endian := .little, pointerWidth := .w16 } : TargetDataLayout) =
    some (Size.ofBytes 32767) := by decide
example : Size.checkedAdd (Size.ofBytes 32767) (Size.ofBytes 1)
    ({ endian := .little, pointerWidth := .w16 } : TargetDataLayout) = none :=
  Verification.checkedAdd_rejects_obj_size_bound_16
example : Size.checkedAdd (Size.ofBytes 2147483647) (Size.ofBytes 0)
    ({ endian := .big, pointerWidth := .w32 } : TargetDataLayout) =
    some (Size.ofBytes 2147483647) := by decide
example : Size.checkedAdd (Size.ofBytes 2147483647) (Size.ofBytes 1)
    ({ endian := .big, pointerWidth := .w32 } : TargetDataLayout) = none := by decide
example {α : Type} [HasDataLayout α] (size offset : Size) (cx : α) (result : Size)
    (h : Size.checkedAdd size offset cx = some result) :
    result.bytes < (HasDataLayout.dataLayout cx).objSizeBound :=
  Verification.checkedAdd_success_below_bound size offset cx result h
example : Size.checkedAdd (Size.ofBytes 2305843009213693951) (Size.ofBytes 0)
    ({ endian := .little, pointerWidth := .w64 } : TargetDataLayout) =
    some (Size.ofBytes 2305843009213693951) := by decide
example : Size.checkedAdd (Size.ofBytes 2305843009213693951) (Size.ofBytes 1)
    ({ endian := .little, pointerWidth := .w64 } : TargetDataLayout) = none := by decide
example : Size.checkedAdd (Size.ofBytes 18446744073709551615) (Size.ofBytes 1)
    ({ endian := .little, pointerWidth := .w64 } : TargetDataLayout) = none := by decide
example : Size.checkedMul (Size.ofBytes 3) 4
    ({ endian := .little, pointerWidth := .w16 } : TargetDataLayout) =
    some (Size.ofBytes 12) := by decide

example : Align.fromBytes 0 = .ok Align.ONE := by decide
example : Align.fromBytes 3 = .error (.notPowerOfTwo 3) := by decide
example : Align.fromBytes 536870912 = .ok Align.MAX := by decide
example : Align.fromBytes 1073741824 = .error (.tooLarge 1073741824) := by decide
example : Align.fromBits 9 = .ok (Align.mk 1) := by decide
example : (Align.maxForTarget
    ({ endian := .little, pointerWidth := .w16 } : TargetDataLayout)).pow2 = 15 := by decide
example : (Align.maxForTarget
    ({ endian := .little, pointerWidth := .w64 } : TargetDataLayout)).pow2 = 29 := by decide
example : Align.bytes (Align.maxAlignedFactor (Size.ofBytes 0)) =
    .error (.shiftOverflow 64) := by decide
example : (Align.restrictForOffset Align.EIGHT (Size.ofBytes 0)).pow2 = 3 := by decide
example : Size.alignTo (Size.ofBytes 5) Align.EIGHT = .ok (Size.ofBytes 8) := by decide
example : Size.alignTo (Size.ofBytes 18446744073709551615) Align.EIGHT =
    .error (.sizeOverflow (Size.ofBytes 18446744073709551615) 7) := by decide
example : Size.isAligned (Size.ofBytes 16) Align.EIGHT = .ok true := by decide
example : Size.isAligned (Size.ofBytes 17) Align.EIGHT = .ok false := by decide

example : Size.truncate (Size.ofBytes 0) (BitVec.ofNat 128 255) = .ok 0 := by decide
example : Size.truncate (Size.ofBytes 1) (BitVec.ofNat 128 511) =
    .ok (BitVec.ofNat 128 255) := by decide
example : Size.truncate (Size.ofBytes 16) (BitVec.ofNat 128 (2^128 - 1)) =
    .ok (BitVec.ofNat 128 (2^128 - 1)) := by decide
example : Size.truncate (Size.ofBytes 17) 0 =
    .error (.integerWidthTooLarge 136) := by decide
example : Size.signExtend (Size.ofBytes 1) (BitVec.ofNat 128 255) = .ok (-1) := by decide
example : Size.signExtend (Size.ofBytes 8) (BitVec.ofNat 128 (2^63)) =
    .ok (-9223372036854775808) := by decide
example : Size.signExtend (Size.ofBytes 16) (BitVec.ofNat 128 (2^127)) =
    .ok (-170141183460469231731687303715884105728) := by decide
example : Size.unsignedIntMax (Size.ofBytes 16) =
    .ok (BitVec.ofNat 128 (2^128 - 1)) := by decide
example : Size.signedIntMin (Size.ofBytes 16) =
    .ok (-170141183460469231731687303715884105728) := by decide
example : Size.unsignedIntMax (Size.ofBytes 0) = .error .zeroWidthUnsignedBound := by decide
example : Size.signedIntMin (Size.ofBytes 0) = .error .zeroWidthSignedBound := by decide

example : Endian.asString .little = "little" := by decide
example : Endian.parse "big" = .ok .big := by decide
example : Endian.parse "middle" = .error "unknown endian: \"middle\"" := by decide
example : (AbiAlign.min (AbiAlign.new Align.EIGHT) (AbiAlign.new Align.ONE)).abi = Align.ONE := by decide
example : (AbiAlign.max (AbiAlign.new Align.EIGHT) (AbiAlign.new Align.ONE)).abi = Align.EIGHT := by decide

private def u128 (value : Nat) : U128 := BitVec.ofNat 128 value

example : WrappingRange.contains ⟨u128 254, u128 2⟩ (u128 1) = true := by decide
example : WrappingRange.contains ⟨u128 254, u128 2⟩ (u128 3) = false := by decide
example : WrappingRange.isFullFor ⟨u128 128, u128 127⟩ (Size.ofBytes 1) = .ok true := by decide
example : WrappingRange.noUnsignedWraparound ⟨u128 254, u128 2⟩
    (Size.ofBytes 1) = .ok .wrapping := by decide
example : WrappingRange.noSignedWraparound ⟨u128 254, u128 2⟩
    (Size.ofBytes 1) = .ok .nonWrapping := by decide
example : WrappingRange.smallestRangeContaining [u128 1, u128 254]
    (Size.ofBytes 1) = .ok (some ⟨u128 254, u128 1⟩) := by decide
example : WrappingRange.smallestRangeContaining [u128 10, u128 11, u128 30, u128 39]
    (Size.ofBytes 2) = .ok (some ⟨u128 10, u128 39⟩) := by decide
example : WrappingRange.containsRange ⟨u128 254, u128 2⟩ ⟨u128 255, u128 1⟩
    (Size.ofBytes 1) = .ok true := by decide
