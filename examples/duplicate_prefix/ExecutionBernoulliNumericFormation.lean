import duplicate_prefix.ExecutionAddressSlackFormation
namespace DuplicatePrefix.ExecutionBernoulliNumericFormation
open Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def exponent (bits : UInt64) : Nat := (bits.toNat/2^52)%2^11

def parts (bits : UInt64) : Bool × Nat × Nat :=
  let exp:=exponent bits
  let fraction:=bits.toNat%2^52
  let significand:=if exp=0 then fraction else 2^52+fraction
  let unbiased : Int:=if exp=0 then -1022 else Int.ofNat exp-1023
  let scaled:=if unbiased-52≥0 then (significand*2^(unbiased-52).toNat,1)
    else (significand,2^(-(unbiased-52)).toNat)
  (bits.toNat/2^63 != 0,scaled.1,scaled.2)

def Valid (bits : UInt64) : Prop :=
  exponent bits≠2047 ∧ (parts bits).2.2≠0 ∧ (parts bits).2.1≤(parts bits).2.2 ∧
    ((parts bits).1 && ((parts bits).2.1 != 0))=false

def Legal (bits : UInt64) (choice : Bool) : Prop :=
  Valid bits ∧ if choice then 0<(parts bits).2.1*2^64/(parts bits).2.2
    else (parts bits).2.1*2^64/(parts bits).2.2<2^64

theorem decode (bits : UInt64) (finite : exponent bits≠2047) :
    (FloatBits.mk .binary64 (BitVec.ofNat 128 bits.toNat)).decode=
      .ok ⟨(parts bits).1,.finite (parts bits).2.1 (parts bits).2.2⟩ := by
  have bound : bits.toNat<2^128 := Nat.lt_trans bits.toNat_lt (by decide)
  unfold FloatBits.decode
  unfold_internal ".FloatBits.powScale"
  simp only [FloatFormat.width,FloatFormat.fractionBits,FloatFormat.exponentBits,FloatFormat.minExponent,FloatFormat.bias,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt bound,show ¬bits.toNat≥2^64 from Nat.not_le.mpr bits.toNat_lt,
    show 64-11-1=52 from rfl,show 64-1=63 from rfl,show 2^11-1=2047 from rfl,
    show ¬(bits.toNat/2^52)%2^11=2047 from finite,beq_iff_eq,↓reduceIte,
    exponent,parts,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,Nat.one_mul]
  rfl

theorem permits (bits : UInt64) (valid : Valid bits) (choice : Bool) :
    TerminatorMachine.permitsPreemption bits choice=
      .ok (if choice then decide (0<(parts bits).2.1*2^64/(parts bits).2.2)
        else decide ((parts bits).2.1*2^64/(parts bits).2.2<2^64)) := by
  have raw:=decode bits valid.1
  unfold TerminatorMachine.permitsPreemption
  simp only [raw,Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,
    show ((parts bits).2.2==0)=false from by simpa using valid.2.1,
    show ¬(parts bits).2.1>(parts bits).2.2 from Nat.not_lt.mpr valid.2.2.1,
    valid.2.2.2,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  cases choice <;> rfl

def consumed (tape : Tape) (site : BoolSite) (bits : UInt64) (choice : Bool) : Tape :=
  {tape with cursor:=tape.cursor+1,events:=tape.events.push ⟨.bernoulli site bits,.boolean site choice⟩}

/-- Actual Bernoulli action success follows from raw IEEE/rational support and
one supplied typed event. No demand/choice-action success is an assumption. -/
theorem bernoulli {S} (access : Access S) (before : S) (site : BoolSite) (bits : UInt64) (choice : Bool)
    (legal : Legal bits choice)
    (supplied : (access.get before).inputs[(access.get before).cursor]?=some (.boolean site choice)) :
    ExecutionChoices.bernoulli access site bits before=
      .ok choice (access.put before (consumed (access.get before) site bits choice)) := by
  have bounded : (access.get before).cursor<(access.get before).inputs.size := by
    by_cases valid : (access.get before).cursor<(access.get before).inputs.size
    · exact valid
    · rw [Array.getElem?_eq_none (by omega)] at supplied
      cases supplied
  have selected : TerminatorMachine.permitsPreemption bits choice=.ok true := by
    rw [permits bits legal.1 choice]
    cases choice
    · change Except.ok (decide ((parts bits).2.1*2^64/(parts bits).2.2<2^64))=Except.ok true
      have support : (parts bits).2.1*2^64/(parts bits).2.2<2^64:=legal.2
      simp only [support,decide_true]
    · change Except.ok (decide (0<(parts bits).2.1*2^64/(parts bits).2.2))=Except.ok true
      have support : 0<(parts bits).2.1*2^64/(parts bits).2.2:=legal.2
      simp only [support,decide_true]
  unfold ExecutionChoices.bernoulli
  unfold_internal ".ExecutionChoices.demand"
  unfold_internal ".ExecutionChoices.consume"
  simp only [permits bits legal.1 false,selected,show ¬(access.get before).cursor>(access.get before).inputs.size from by omega,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    supplied,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,consumed]
end DuplicatePrefix.ExecutionBernoulliNumericFormation
