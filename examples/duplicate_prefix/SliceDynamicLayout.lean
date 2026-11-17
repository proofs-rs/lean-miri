import duplicate_prefix.CopyIntrinsic
import Miri.Interpreter.DynamicLayout

/-! Actual dynamic sizing of the u8 slice carried by a fat pointer. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace DuplicatePrefix.SliceDynamicLayout
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem u8_slice_size {S C : Type}
    (h : DynamicLayoutHooks Provenance S C) (choice : C) (fuel : Nat)
    (layout element : TyAndLayout TyId) (len : UInt64)
    (unsized : layout.layout.isSized = false)
    (kind : h.classify choice layout.ty = pure .slice)
    (field : h.field choice layout 0 = pure element)
    (elementSize : element.layout.size = Size.ofBytes 1)
    (elementAlign : element.layout.align.abi = Align.ONE)
    (width : h.target.pointerWidth = .w64)
    (bounded : len ≤ h.maxSizeOfVal.bytes) :
    DynamicLayout.sizeAndAlignFromMeta h choice (fuel + 1)
      (.metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))) layout =
      pure (some (Size.ofBytes len, Align.ONE)) := by
  funext state
  have lengthBound : len.toNat ≤ 2 ^ 64 - 1 := by
    have limit : len.toNat < 18446744073709551616 := len.toNat_lt_size
    omega
  have notTooBig : ¬ len > h.maxSizeOfVal.bytes := by
    have boundNat := UInt64.le_iff_toNat_le.mp bounded
    simp only [UInt64.lt_iff_toNat_lt]
    omega
  unfold DynamicLayout.sizeAndAlignFromMeta
  simp only [unsized, Bool.false_eq_true, ↓reduceIte, kind, bind, EStateM.bind,
    pure, EStateM.pure]
  unfold_internal ".DynamicLayout.metadataScalar"
  unfold_internal ".DynamicLayout.liftResult"
  simp only [MemPlaceMeta.unwrapMeta, width, PointerWidth.bits,
    CopyIntrinsic.usize_scalar_roundtrip, Except.mapError,
    bind, EStateM.bind, pure, EStateM.pure, field, elementSize, elementAlign,
    Size.ofBytes, UInt64.toNat_ofNat, Nat.one_mul,
    Nat.min_eq_left lengthBound, UInt64.ofNat_toNat, notTooBig, ↓reduceIte]
  erw [CopyIntrinsic.usize_scalar_roundtrip]
  simp [Nat.min_eq_left lengthBound, UInt64.ofNat_toNat, notTooBig,
    bind, EStateM.bind, pure, EStateM.pure]

#print axioms u8_slice_size
end DuplicatePrefix.SliceDynamicLayout

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.SliceDynamicLayout.u8_slice_size) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "u8_slice_size depends on unapproved axiom {dependency}"
