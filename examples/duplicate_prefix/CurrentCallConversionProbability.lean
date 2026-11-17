import duplicate_prefix.ExecutionBernoulliNumericFormation
import Miri.Memory.AllocAddresses.ReusePool

/-! The real reuse-pool probability support follows from the raw IEEE
Bernoulli support. No independent relation between two probability models is
an input. -/
namespace DuplicatePrefix.CurrentCallConversionProbability
open Miri.Memory.AllocAddresses
open ExecutionBernoulliNumericFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 2048

private theorem normal_bound (bits : UInt64) (valid : Valid bits)
    (normal : exponent bits≠0) :
    exponent bits≤1023 ∧ (exponent bits=1023→bits.toNat%2^52=0) := by
  have fractionBound := Nat.mod_lt bits.toNat (show 0<2^52 by decide)
  have magnitude := valid.2.2.1
  unfold parts at magnitude
  simp only [normal,↓reduceIte] at magnitude
  simp only [Int.ofNat_eq_natCast] at magnitude
  split at magnitude
  · have positive : 0<2^((Int.ofNat (exponent bits)-1023-52).toNat) := Nat.pow_pos (by decide)
    have lower : 2^52+bits.toNat%2^52 ≤
        (2^52+bits.toNat%2^52)*2^((Int.ofNat (exponent bits)-1023-52).toNat) :=
      Nat.le_mul_of_pos_right _ positive
    simp only [Int.ofNat_eq_natCast] at lower
    omega
  · rename_i small
    have en : exponent bits≤1074 := by omega
    have nexp : (-((exponent bits:Int)-1023-52)).toNat=1075-exponent bits := by omega
    rw [nexp] at magnitude
    have bound : exponent bits≤1023 := by
      by_cases large : exponent bits≤1023
      · exact large
      ·
        have power : 2^(1075-exponent bits)≤2^51 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
    refine ⟨bound,?_⟩
    intro equal
    rw [equal] at magnitude
    simp only [Nat.reduceSub,Nat.reducePow] at magnitude
    omega

private theorem unpack_shape (rate : Float) (valid : Valid rate.toBits) :
    rate.toModel.unpack =
      let e:=exponent rate.toBits
      let f:=rate.toBits.toNat%2^52
      let sign:=if rate.toBits.toNat/2^63=0 then Float.Model.UnpackedFloat.Sign.positive else .negative
      if e=0 then
        if h:f=0 then .zero sign else .finite sign f (-1074) (by omega)
      else .finite sign (2^52+f) ((e:Int)-1075) (by omega) := by
  have signBound : rate.toBits.toNat/2^63<2 := by have h:=rate.toBits.toNat_lt; omega
  have appended : (1#1 ++ BitVec.extractLsb' 0 52 rate.toModel.toBits.toBitVec).toNat=
      2^52+rate.toBits.toNat%2^52 := by
    rw [BitVec.toNat_append,←Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _)]
    simp only [BitVec.toNat_ofNat,Nat.shiftLeft_eq,BitVec.extractLsb'_toNat,
      UInt64.toNat_toBitVec,Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow,Nat.reduceMod,Nat.one_mul,Nat.div_one,Float.toBits]
  have finite:=valid.1
  unfold exponent at finite
  simp only [Float.toBits] at *
  unfold Float.Model.unpack Float.Model.UnpackedFloat.unpack
  simp only [Float.Model.UnpackedFloat.unpackMantissa,Float.Model.UnpackedFloat.unpackExponent,
    Float.Model.UnpackedFloat.unpackSign,Float.Model.Format.binary64,Float.Model.Format.exponentBias]
  simp only [←BitVec.toNat_inj,BitVec.extractLsb'_toNat,UInt64.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,BitVec.toNat_neg]
  simp only [Nat.reducePow,Nat.reduceSub,Nat.reduceMod,Nat.div_one,Nat.zero_mod,
    exponent,appended]
  simp only [Nat.reducePow] at finite signBound
  simp only [finite,↓reduceIte]
  unfold Float.Model.UnpackedFloat.Sign.ofBitVec
  simp only [←BitVec.toNat_inj,BitVec.extractLsb'_toNat,UInt64.toNat_toBitVec,
    Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat,Nat.reduceAdd,Nat.reducePow,Nat.zero_mod,
    Nat.mod_eq_of_lt signBound]
  split
  · rename_i e0
    simp [e0]
  · rename_i e0
    simp (config := { implicitDefEqProofs := true }) only [e0,↓reduceIte]
    congr 1 <;> omega

private theorem numerator_zero (bits : UInt64) :
    (parts bits).2.1=0 ↔ exponent bits=0 ∧ bits.toNat%2^52=0 := by
  by_cases zero : exponent bits=0
  · simp [parts,zero]
  · simp only [parts,zero,↓reduceIte]
    split
    · have positive : 0<2^((Int.ofNat (exponent bits)-1023-52).toNat) := Nat.pow_pos (by decide)
      have num : 0<(2^52+bits.toNat%2^52)*2^((Int.ofNat (exponent bits)-1023-52).toNat) :=
        Nat.mul_pos (by omega) positive
      simp only [false_and,iff_false]
      exact Nat.ne_of_gt num
    · simp only [false_and,iff_false]
      omega

private theorem valid_sign (bits : UInt64) (valid : Valid bits) :
    bits.toNat/2^63=0 ∨ (exponent bits=0 ∧ bits.toNat%2^52=0) := by
  by_cases positive : bits.toNat/2^63=0
  · exact Or.inl positive
  · right
    apply (numerator_zero bits).mp
    have sign:=(valid.2.2.2)
    change ((bits.toNat/2^63!=0) && ((parts bits).2.1!=0))=false at sign
    simpa [positive] using sign

private theorem zero_unpack : (0.0:Float).toModel.unpack=.zero .positive := rfl
private theorem one_unpack : (1.0:Float).toModel.unpack=.finite .positive (2^52) (-52) (by decide) := rfl

private theorem comparisons (rate : Float) (valid : Valid rate.toBits) :
    Float.le 0.0 rate=true ∧ Float.le rate 1.0=true ∧
      ((parts rate.toBits).2.1≠0→Float.lt 0.0 rate=true) ∧
      (exponent rate.toBits≠1023→Float.lt rate 1.0=true) := by
  have shape:=unpack_shape rate valid
  have sign:=valid_sign rate.toBits valid
  simp only [Float.le,Float.lt,decide_eq_true_eq]
  change (Float.Model.UnpackedFloat.le (0.0:Float).toModel.unpack rate.toModel.unpack=true) ∧
    (Float.Model.UnpackedFloat.le rate.toModel.unpack (1.0:Float).toModel.unpack=true) ∧
    ((parts rate.toBits).2.1≠0→Float.Model.UnpackedFloat.lt (0.0:Float).toModel.unpack rate.toModel.unpack=true) ∧
    (exponent rate.toBits≠1023→Float.Model.UnpackedFloat.lt rate.toModel.unpack (1.0:Float).toModel.unpack=true)
  rw [zero_unpack,one_unpack,shape]
  by_cases e0 : exponent rate.toBits=0
  · simp only [e0,↓reduceIte]
    by_cases f0 : rate.toBits.toNat%2^52=0
    · simp only [f0,↓reduceDIte]
      cases sign with
      | inl positive => simp [Float.Model.UnpackedFloat.le,Float.Model.UnpackedFloat.lt,
          Float.Model.UnpackedFloat.compare,numerator_zero,e0,f0]
      | inr zero =>
        split <;> simp [Float.Model.UnpackedFloat.le,Float.Model.UnpackedFloat.lt,
          Float.Model.UnpackedFloat.compare,numerator_zero,e0,f0]
    · have positive : rate.toBits.toNat/2^63=0 := by rcases sign with h|h;exact h;omega
      have cmp : compare (-1074:Int) (-52)=.lt := by decide
      simp [f0,positive,cmp,Float.Model.UnpackedFloat.le,Float.Model.UnpackedFloat.lt,
        Float.Model.UnpackedFloat.compare]
  · have positive : rate.toBits.toNat/2^63=0 := by rcases sign with h|h;exact h;omega
    have bound:=normal_bound rate.toBits valid e0
    simp only [e0,positive,↓reduceIte]
    by_cases top : exponent rate.toBits=1023
    · have fraction:=bound.2 top
      simp [top,fraction,Float.Model.UnpackedFloat.le,Float.Model.UnpackedFloat.lt,
        Float.Model.UnpackedFloat.compare]
    · have less : (exponent rate.toBits:Int)-1075 < -52 := by omega
      have cmp : compare ((exponent rate.toBits:Int)-1075) (-52)=.lt := Int.compare_eq_lt.mpr less
      simp [Float.Model.UnpackedFloat.le,Float.Model.UnpackedFloat.lt,
        Float.Model.UnpackedFloat.compare,cmp]

/-- Both actual pool choices follow from the existing raw Bernoulli legality.
This includes signed zero and subnormal probabilities. -/
theorem allowed (rate : Float) (choice : Bool) (legal : Legal rate.toBits choice) :
    ReusePool.bernoulliChoiceAllowed rate choice=true := by
  rcases comparisons rate legal.1 with ⟨lower,upper,positive,belowOne⟩
  have supported : (if choice then Float.lt 0.0 rate else Float.lt rate 1.0)=true := by
    cases choice
    · apply belowOne
      intro top
      have normal : exponent rate.toBits≠0 := by omega
      have fraction := (normal_bound rate.toBits legal.1 normal).2 top
      have raw := legal.2
      simp [parts,top,fraction] at raw
    · apply positive
      intro zero
      have raw := legal.2
      change 0<(parts rate.toBits).2.1*2^64/(parts rate.toBits).2.2 at raw
      simp only [zero,Nat.zero_mul,Nat.zero_div] at raw
      exact Nat.not_lt_zero _ raw
  unfold ReusePool.bernoulliChoiceAllowed
  unfold_internal ".ReusePool.validRate"
  simp only [lower,upper,Bool.true_and,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  exact supported

end DuplicatePrefix.CurrentCallConversionProbability

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionProbability.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved probability bridge dependency {name}: {dependency}"
