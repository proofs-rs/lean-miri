import empty_function.PolicyChoiceSupply
namespace EmptyFunction.DiagnosticChoiceSupport
open Miri Miri.Interpreter ExecutionChoices
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- Pure decoded probability information follows from the source probability
query. It contains no machine operation or choice-consumer success premise. -/
structure Probability (bits : UInt64) where
  decoded : FloatDecoded
  numerator : Nat
  denominator : Nat
  decode : (FloatBits.mk .binary64 (BitVec.ofNat 128 bits.toNat)).decode = .ok decoded
  finite : decoded.value = .finite numerator denominator
  valid : (denominator == 0 || numerator > denominator || (decoded.negative && numerator != 0)) = false

theorem probability (bits : UInt64) (allowed : Bool)
    (valid : TerminatorMachine.permitsPreemption bits false = .ok allowed) :
    Nonempty (Probability bits) := by
  unfold TerminatorMachine.permitsPreemption at valid
  cases hd : (FloatBits.mk .binary64 (BitVec.ofNat 128 bits.toNat)).decode with
  | error e => simp [hd,Except.mapError,bind,Except.bind,pure,Except.pure,throw] at valid
  | ok decoded =>
    cases hv : decoded.value with
    | infinite => simp [hd,hv,Except.mapError,bind,Except.bind,pure,Except.pure,throw] at valid
    | nan payload => simp [hd,hv,Except.mapError,bind,Except.bind,pure,Except.pure,throw] at valid
    | finite n d =>
      by_cases bad : (d == 0 || n > d || (decoded.negative && n != 0)) = true
      · simp [hd,hv,bad,Except.mapError,bind,Except.bind,pure,Except.pure,throw] at valid
      · exact ⟨⟨decoded,n,d,hd,hv,Bool.eq_false_iff.mpr bad⟩⟩

theorem permits (bits : UInt64) (p : Probability bits) (choice : Bool) :
    TerminatorMachine.permitsPreemption bits choice =
      .ok (if choice then p.numerator * 2^64 / p.denominator > 0
        else p.numerator * 2^64 / p.denominator < 2^64) := by
  simp [TerminatorMachine.permitsPreemption,p.decode,p.finite,p.valid,Except.mapError,bind,Except.bind,pure,Except.pure,throw]

/-- A valid source rate has at least one admissible Bernoulli result. -/
theorem support_nonempty (bits : UInt64) (validFalse : Bool)
    (valid : TerminatorMachine.permitsPreemption bits false = .ok validFalse) :
    ∃ allowedTrue : Bool,
      TerminatorMachine.permitsPreemption bits true = .ok allowedTrue ∧
      (validFalse || allowedTrue) = true := by
  obtain ⟨p⟩ := probability bits validFalse valid
  refine ⟨decide (p.numerator * 2^64 / p.denominator > 0),permits bits p true,?_⟩
  have hf := permits bits p false
  rw [valid] at hf
  have eq := Except.ok.inj hf
  cases validFalse with
  | true => rfl
  | false =>
    have notLess : ¬ p.numerator * 2^64 / p.denominator < 2^64 := by
      simpa using eq.symm
    have positive : p.numerator * 2^64 / p.denominator > 0 := by omega
    simp only [Bool.false_or,decide_eq_true_eq]
    exact positive

/-- Every 64-bit word selects an admitted outcome. No property of SplitMix,
its seed, or its probability distribution is required. -/
theorem word_supported (bits : UInt64) (p : Probability bits) (word : UInt64)
    (falseAllowed : TerminatorMachine.permitsPreemption bits false = .ok true)
    (trueAllowed : TerminatorMachine.permitsPreemption bits true = .ok true) :
    TerminatorMachine.permitsPreemption bits
      (word.toNat < p.numerator * 2^64 / p.denominator) = .ok true := by
  cases h : (decide (word.toNat < p.numerator * 2^64 / p.denominator)) with
  | false => simpa [h] using falseAllowed
  | true => simpa [h] using trueAllowed


open EmptyFunction.ChoiceSupply EmptyFunction.PolicyChoiceSupply

/-- Numeric and probability legality only; neither source consumer nor any
memory operation is required to have succeeded. -/
def Ready : AddressRequest → Prop
  | .index _ count => 0 < count
  | .bernoulli _ bits => ∃ allowed : Bool,
      TerminatorMachine.permitsPreemption bits false = .ok allowed

theorem zero_exists (request : AddressRequest) (ready : Ready request) :
    ∃ input, RawZeroValue request input := by
  cases request with
  | index kind count => exact ⟨_,.index kind count ready⟩
  | bernoulli kind bits =>
    obtain ⟨allowed,valid⟩ := ready
    obtain ⟨allowedTrue,ht,nonempty⟩ := support_nonempty bits allowed valid
    cases allowed with
    | true => exact ⟨_,.bernoulliFalse kind bits valid⟩
    | false =>
      have ht' : allowedTrue = true := by simpa using nonempty
      subst allowedTrue
      exact ⟨_,.bernoulliTrue kind bits valid ht⟩

theorem seed_exists (request : AddressRequest) (ready : Ready request) (word : UInt64) :
    ∃ input, RawSeedValue request word input := by
  cases request with
  | index kind count => exact ⟨_,.index kind count word ready⟩
  | bernoulli kind bits =>
    obtain ⟨allowed,valid⟩ := ready
    obtain ⟨p⟩ := probability bits allowed valid
    obtain ⟨allowedTrue,ht,nonempty⟩ := support_nonempty bits allowed valid
    cases allowed with
    | false =>
      have ht' : allowedTrue = true := by simpa using nonempty
      subst allowedTrue
      exact ⟨_,.bernoulliTrue kind bits word valid ht⟩
    | true =>
      cases allowedTrue with
      | false => exact ⟨_,.bernoulliFalse kind bits word valid ht⟩
      | true => exact ⟨_,.bernoulliBoth kind bits word p.decoded p.numerator p.denominator
          valid ht p.decode p.finite⟩

theorem seed_supported {request : AddressRequest} {word : UInt64} {input : Input}
    (value : RawSeedValue request word input) : Supported request input := by
  cases value with
  | index kind count word positive => exact .index kind count _ (Nat.mod_lt _ positive)
  | bernoulliTrue kind rate word hf ht => exact .bernoulli kind rate true false hf ht
  | bernoulliFalse kind rate word hf ht => exact .bernoulli kind rate false true hf hf
  | bernoulliBoth kind rate word decoded n d hf ht encoding finite =>
    refine .bernoulli kind rate _ true hf ?_
    cases h : decide (word.toNat < n*2^64/d) with
    | false => simpa [h] using hf
    | true => simpa [h] using ht

/-- Raw zero-policy selection data computes the actual existing helper. -/
theorem zero_helper {S : Type} (state : S) (maxBytes : Nat)
    {request : AddressRequest} {input : Input} (value : RawZeroValue request input) :
    diagnosticInputSource (sourceRequest request) maxBytes state = .ok input state := by
  cases value with
  | index kind count positive =>
    have nonzero : count ≠ 0 := by omega
    simp [sourceRequest,diagnosticInputSource_index,nonzero,
      bind,EStateM.bind,pure,EStateM.pure]
  | bernoulliFalse kind rate allowed =>
    simp [sourceRequest,diagnosticInputSource_bernoulli,allowed,
      bind,EStateM.bind,pure,EStateM.pure]
  | bernoulliTrue kind rate hf ht =>
    simp [sourceRequest,diagnosticInputSource_bernoulli,hf,ht,
      bind,EStateM.bind,pure,EStateM.pure]

/-- Every source seed/stream state computes its exact existing helper output.
The next RNG state is the actual nextDiagnosticWordSource result. -/
theorem seed_helper {S : Type} (state : S) (maxBytes : Nat)
    (seed rng : UInt64) (first : Bool) (word nextRng : UInt64)
    (mix : nextDiagnosticWordSource (if first then seed else rng) = (word,nextRng))
    {request : AddressRequest} {input : Input} (value : RawSeedValue request word input) :
    seededDiagnosticInputSource (sourceRequest request) maxBytes seed rng first state =
      .ok (input,nextRng) state := by
  cases value with
  | index kind count word positive =>
    have nonzero : count ≠ 0 := by omega
    simp [sourceRequest,seededDiagnosticInputSource_index,nonzero,mix,
      bind,EStateM.bind,pure,EStateM.pure]
  | bernoulliTrue kind rate word hf ht =>
    simp [sourceRequest,seededDiagnosticInputSource_bernoulli,hf,ht,mix,
      bind,EStateM.bind,pure,EStateM.pure]
  | bernoulliFalse kind rate word hf ht =>
    simp [sourceRequest,seededDiagnosticInputSource_bernoulli,hf,ht,mix,
      bind,EStateM.bind,pure,EStateM.pure]
  | bernoulliBoth kind rate word decoded n d hf ht encoding finite =>
    simp [sourceRequest,seededDiagnosticInputSource_bernoulli,hf,ht,mix,encoding,finite,
      bind,EStateM.bind,pure,EStateM.pure]

/-- Every ready request is admitted by the bounded zero policy whenever the
raw cursor and generation quota permit its next draw. -/
theorem diagnostic_step (request : AddressRequest) (ready : Ready request)
    (before : Tape) (maximum bytes : Nat)
    (policy : before.policy = .boundedDiagnostic maximum bytes)
    (cursor : before.cursor = before.inputs.size) (quota : before.generatedChoices < maximum) :
    ∃ input after, Supported request input ∧ PolicyStep request before input after := by
  obtain ⟨input,value⟩ := zero_exists request ready
  exact ⟨input,_,zero_supported value,
    .diagnostic request before input maximum bytes policy cursor quota value⟩

/-- The same raw quota condition admits the actual next seeded draw for every
seed and current RNG state, including the source's first-generation seed rule. -/
theorem seeded_step (request : AddressRequest) (ready : Ready request)
    (before : Tape) (maximum bytes : Nat) (seed : UInt64)
    (policy : before.policy = .boundedSeededDiagnostic maximum bytes seed)
    (cursor : before.cursor = before.inputs.size) (quota : before.generatedChoices < maximum) :
    ∃ input after, Supported request input ∧ PolicyStep request before input after := by
  cases mix : nextDiagnosticWordSource
      (if before.generatedChoices == 0 then seed else before.diagnosticRngState) with
  | mk word nextRng =>
    obtain ⟨input,value⟩ := seed_exists request ready word
    exact ⟨input,_,seed_supported value,
      .diagnosticSeeded request before input maximum bytes seed word nextRng
        policy cursor quota mix value⟩

end EmptyFunction.DiagnosticChoiceSupport

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.DiagnosticChoiceSupport.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic support axiom {name}: {dependency}"
  logInfo m!"Audited {count} diagnostic support declarations"
