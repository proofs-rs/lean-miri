import empty_function.ChoiceSupply
namespace EmptyFunction.ChoiceFloatSupport
open Float.Model
open Miri Miri.Memory Miri.Interpreter
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
private theorem unpack_zero (p : Float) (lo : Float.le 0.0 p = true) (no : Float.lt 0.0 p = false) :
    p.toModel.unpack = .zero .positive ∨ p.toModel.unpack = .zero .negative := by
  change (UnpackedFloat.le (.zero .positive) p.toModel.unpack) = true at lo
  change (UnpackedFloat.lt (.zero .positive) p.toModel.unpack) = false at no
  cases h : p.toModel.unpack with
  | notANumber => simp [h,UnpackedFloat.le,UnpackedFloat.compare] at lo
  | infinity s => cases s <;> simp_all [UnpackedFloat.le,UnpackedFloat.lt,UnpackedFloat.compare]
  | zero s => cases s <;> simp
  | finite s m e pos => cases s <;> simp_all [UnpackedFloat.le,UnpackedFloat.lt,UnpackedFloat.compare]
private theorem bits_zero (p : Float) (h : p.toModel.unpack = .zero .positive ∨ p.toModel.unpack = .zero .negative) :
    p.toBits = 0 ∨ p.toBits = 9223372036854775808 := by
  unfold Float.Model.unpack UnpackedFloat.unpack at h
  dsimp only at h
  split at h
  · split at h <;> simp_all
  · split at h
    · split at h
      · rename_i e0 m0
        have ex := congrArg BitVec.toNat e0
        have ma := congrArg BitVec.toNat m0
        simp only [UnpackedFloat.unpackExponent,UnpackedFloat.unpackMantissa,
          BitVec.extractLsb'_toNat, Format.binary64] at ex ma
        simp only [BitVec.toNat_ofNat, UInt64.toNat_toBitVec, Nat.shiftRight_eq_div_pow] at ex ma
        apply Or.imp (fun x => UInt64.toNat_inj.mp x) (fun x => UInt64.toNat_inj.mp x)
        change p.toModel.toBits.toNat = 0 ∨ p.toModel.toBits.toNat = 9223372036854775808
        have bound := p.toModel.toBits.toNat_lt
        omega
      · simp_all
    · simp_all
private theorem unpack_one (p : Float) (hi : Float.le p 1.0 = true) (no : Float.lt p 1.0 = false) :
    p.toModel.unpack = .finite .positive 4503599627370496 (-52) (by decide) := by
  change UnpackedFloat.le p.toModel.unpack (.finite .positive 4503599627370496 (-52) (by decide)) = true at hi
  change UnpackedFloat.lt p.toModel.unpack (.finite .positive 4503599627370496 (-52) (by decide)) = false at no
  cases h : p.toModel.unpack with
  | notANumber => simp [h,UnpackedFloat.le,UnpackedFloat.compare] at hi
  | infinity s => cases s <;> simp_all [UnpackedFloat.le,UnpackedFloat.lt,UnpackedFloat.compare]
  | zero s => cases s <;> simp_all [UnpackedFloat.le,UnpackedFloat.lt,UnpackedFloat.compare]
  | finite s m e pos =>
    cases s
    · simp [h,UnpackedFloat.lt,UnpackedFloat.compare] at no
    · rw [h] at no
      change (some ((compare e (-52)).then (compare m 4503599627370496)) == some .lt) = false at no
      simp only [UnpackedFloat.le,UnpackedFloat.compare] at hi
      have equal : (compare e (-52)).then (compare m 4503599627370496) = .eq := by
        cases ce : compare e (-52) <;> cases cm : compare m 4503599627370496 <;>
          simp_all [Ordering.then]
      have exp : e = -52 := Int.compare_eq_eq.mp (by
        cases ce : compare e (-52) <;> simp_all [Ordering.then])
      have mant : m = 4503599627370496 := Nat.compare_eq_eq.mp (by
        simpa [exp,Ordering.then] using equal)
      subst e; subst m; rfl
private theorem bits_one (p : Float) (h : p.toModel.unpack = .finite .positive 4503599627370496 (-52) (by decide)) :
    p.toBits = 4607182418800017408 := by
  unfold Float.Model.unpack UnpackedFloat.unpack at h
  dsimp only at h
  split at h
  · split at h <;> simp_all
  · split at h
    · split at h
      · simp_all
      · have mant := UnpackedFloat.finite.inj h
        have ma := mant.2.1
        simp only [UnpackedFloat.unpackMantissa,BitVec.extractLsb'_toNat,Format.binary64,
          UInt64.toNat_toBitVec] at ma
        omega
    · have data := UnpackedFloat.finite.inj h
      have ma := data.2.1
      have ex := data.2.2
      simp only [UnpackedFloat.unpackMantissa,UnpackedFloat.unpackExponent,
        BitVec.toNat_append,BitVec.extractLsb'_toNat,Format.binary64,
        UInt64.toNat_toBitVec] at ma ex
      change p.toModel.toBits = 4607182418800017408
      apply UInt64.toNat_inj.mp
      have bound := p.toModel.toBits.toNat_lt
      simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at ma ex
      have sg := data.1
      simp only [UnpackedFloat.unpackSign,UnpackedFloat.Sign.ofBitVec] at sg
      by_cases signzero : BitVec.extractLsb' 63 1 p.toModel.toBits.toBitVec = 0#1
      ·
        have si := congrArg BitVec.toNat signzero
        simp only [BitVec.extractLsb'_toNat,UInt64.toNat_toBitVec,
          BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow] at si
        change ((p.toModel.toBits.toNat / 4503599627370496 % 2048 : Nat) : Int) - (1023 + 52) = -52 at ex
        have lower : p.toModel.toBits.toNat % 4503599627370496 < 2^52 := Nat.mod_lt _ (by decide)
        simp only [Nat.shiftLeft_eq] at ma
        have eqor := Nat.two_pow_add_eq_or_of_lt lower 1
        simp only [Nat.mul_one, Nat.reducePow] at eqor
        simp only [Nat.reducePow, Nat.reduceMod, Nat.div_one, Nat.one_mul] at ma
        rw [← eqor] at ma
        simp only [UInt64.reduceToNat] at *

        omega
      · simp [signzero] at sg


/-- A nonnegative binary64 rate that is not positive is one of the two signed zeros. -/
theorem zero_endpoint (rate : Float) (lower : Float.le 0.0 rate = true)
    (notPositive : Float.lt 0.0 rate = false) :
    rate.toBits = 0 ∨ rate.toBits = 9223372036854775808 :=
  bits_zero rate (unpack_zero rate lower notPositive)

/-- A rate at most one that is not strictly below one has the exact one encoding. -/
theorem one_endpoint (rate : Float) (upper : Float.le rate 1.0 = true)
    (notBelow : Float.lt rate 1.0 = false) : rate.toBits = 4607182418800017408 :=
  bits_one rate (unpack_one rate upper notBelow)

/-- Exact rand support implies the port's endpoint support check. The converse
is deliberately absent: tiny positive probabilities may have zero rand threshold. -/
theorem allowed_of_permits (rate : Float) (value : Bool)
    (lower : Float.le 0.0 rate = true) (upper : Float.le rate 1.0 = true)
    (support : TerminatorMachine.permitsPreemption rate.toBits value = .ok true) :
    AllocAddresses.ReusePool.bernoulliChoiceAllowed rate value = true := by
  change (if !(Float.le 0.0 rate && Float.le rate 1.0) then false
    else if value then Float.lt 0.0 rate else Float.lt rate 1.0) = true
  rw [lower,upper]
  simp only [Bool.true_and,Bool.not_true,Bool.false_eq_true,ite_false]
  cases value with
  | false =>
    by_cases less : Float.lt rate 1.0 = true
    · exact less
    · have endpoint := one_endpoint rate upper (Bool.eq_false_iff.mpr less)
      rw [endpoint] at support
      have bad : TerminatorMachine.permitsPreemption 4607182418800017408 false = .ok false := by decide +kernel
      rw [bad] at support
      cases support
  | true =>
    by_cases positive : Float.lt 0.0 rate = true
    · exact positive
    · obtain endpoint | endpoint := zero_endpoint rate lower (Bool.eq_false_iff.mpr positive)
      · rw [endpoint] at support
        have bad : TerminatorMachine.permitsPreemption 0 true = .ok false := by decide +kernel
        rw [bad] at support
        cases support
      · rw [endpoint] at support
        have bad : TerminatorMachine.permitsPreemption 9223372036854775808 true = .ok false := by decide +kernel
        rw [bad] at support
        cases support

theorem allowed_of_supported (kind : ChoiceSupply.BoolKind) (rate : Float) (value : Bool)
    (lower : Float.le 0.0 rate = true) (upper : Float.le rate 1.0 = true)
    (supported : ChoiceSupply.Supported (.bernoulli kind rate.toBits) (.boolean kind.site value)) :
    AllocAddresses.ReusePool.bernoulliChoiceAllowed rate value = true := by
  cases supported with
  | bernoulli _ _ _ _ _ support => exact allowed_of_permits rate value lower upper support

end EmptyFunction.ChoiceFloatSupport

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ChoiceFloatSupport.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved float-support axiom: {name}: {dependency}"
