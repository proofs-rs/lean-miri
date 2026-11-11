import empty_function.ChoiceSupply
namespace EmptyFunction.PolicyChoiceSupply
open Miri Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000
/-- Pure selection data for the source zero diagnostic generator. -/
inductive RawZeroValue : AddressRequest → Input → Prop where
  | index (kind : IndexKind) (count : Nat) (positive : 0 < count) :
      RawZeroValue (.index kind count) (.index kind.site 0)
  | bernoulliFalse (kind : BoolKind) (rate : UInt64)
      (allowed : TerminatorMachine.permitsPreemption rate false = .ok true) :
      RawZeroValue (.bernoulli kind rate) (.boolean kind.site false)
  | bernoulliTrue (kind : BoolKind) (rate : UInt64)
      (falseAllowed : TerminatorMachine.permitsPreemption rate false = .ok false)
      (trueAllowed : TerminatorMachine.permitsPreemption rate true = .ok true) :
      RawZeroValue (.bernoulli kind rate) (.boolean kind.site true)

/-- Pure selection data for every source SplitMix word. No seed is fixed and
no stateful choice/address operation occurs in these clauses. -/
inductive RawSeedValue : AddressRequest → UInt64 → Input → Prop where
  | index (kind : IndexKind) (count : Nat) (word : UInt64) (positive : 0 < count) :
      RawSeedValue (.index kind count) word (.index kind.site (word.toNat % count))
  | bernoulliTrue (kind : BoolKind) (rate word : UInt64)
      (falseAllowed : TerminatorMachine.permitsPreemption rate false = .ok false)
      (trueAllowed : TerminatorMachine.permitsPreemption rate true = .ok true) :
      RawSeedValue (.bernoulli kind rate) word (.boolean kind.site true)
  | bernoulliFalse (kind : BoolKind) (rate word : UInt64)
      (falseAllowed : TerminatorMachine.permitsPreemption rate false = .ok true)
      (trueAllowed : TerminatorMachine.permitsPreemption rate true = .ok false) :
      RawSeedValue (.bernoulli kind rate) word (.boolean kind.site false)
  | bernoulliBoth (kind : BoolKind) (rate word : UInt64) (decoded : FloatDecoded) (numerator denominator : Nat)
      (falseAllowed : TerminatorMachine.permitsPreemption rate false = .ok true)
      (trueAllowed : TerminatorMachine.permitsPreemption rate true = .ok true)
      (encoding : (FloatBits.mk .binary64 (BitVec.ofNat 128 rate.toNat)).decode = .ok decoded)
      (finite : decoded.value = .finite numerator denominator) :
      RawSeedValue (.bernoulli kind rate) word
        (.boolean kind.site (word.toNat < numerator*2^64/denominator))

def generated (tape : Tape) (input : Input) : Tape :=
  {tape with inputs := tape.inputs.push input,generatedChoices := tape.generatedChoices+1}

def seeded (tape : Tape) (input : Input) (nextRng : UInt64) : Tape :=
  {generated tape input with diagnosticRngState := nextRng}

/-- Exact raw policy bookkeeping. Supplied entries never require generation
quota; generated entries require quota only at the current exhausted suffix. -/
inductive PolicyStep : AddressRequest → Tape → Input → Tape → Prop where
  | supplied (request : AddressRequest) (before : Tape) (input : Input)
      (head : before.inputs[before.cursor]? = some input) :
      PolicyStep request before input (advance before request input)
  | diagnostic (request : AddressRequest) (before : Tape) (input : Input) (maximum bytes : Nat)
      (policy : before.policy = .boundedDiagnostic maximum bytes)
      (cursor : before.cursor = before.inputs.size) (quota : before.generatedChoices < maximum)
      (value : RawZeroValue request input) :
      PolicyStep request before input (advance (generated before input) request input)
  | diagnosticSeeded (request : AddressRequest) (before : Tape) (input : Input)
      (maximum bytes : Nat) (seed word nextRng : UInt64)
      (policy : before.policy = .boundedSeededDiagnostic maximum bytes seed)
      (cursor : before.cursor = before.inputs.size) (quota : before.generatedChoices < maximum)
      (mix : nextDiagnosticWordSource (if before.generatedChoices == 0 then seed else before.diagnosticRngState) = (word,nextRng))
      (value : RawSeedValue request word input) :
      PolicyStep request before input (advance (seeded before input nextRng) request input)

/-- The response-dependent source plan follows the actual new tape, including
appended diagnostic inputs and RNG changes. Non-choice halts remain admitted. -/
def Fits {budget : Nat} : Plan budget → Tape → Prop
  | .done,_ => True
  | .blocked,_ => False
  | .halted _,_ => True
  | .request request next,tape =>
    ∃ input, ∃ supported : Supported request input, ∃ after,
      PolicyStep request tape input after ∧ Fits (next input supported) after

structure Environment {budget : Nat} (plan : Plan budget) (tape : Tape) : Prop where
  fits : Fits plan tape

/-- Remaining supplied inputs and generated quota contribute additively for
finite policies. Uncapped diagnostic policies have no finite quota (`none`).
This bookkeeping does not assert that a requested draw is supported. -/
def remaining (tape : Tape) : Option Nat :=
  match tape.policy with
  | .strict => some (tape.inputs.size-tape.cursor)
  | .boundedDiagnostic maximum _ | .boundedSeededDiagnostic maximum _ _ =>
    some (tape.inputs.size-tape.cursor + (maximum-tape.generatedChoices))
  | .diagnostic | .seededDiagnostic _ => none

structure AccessLaws {S : Type} (access : Access S) : Prop where
  get_put : ∀ state tape, access.get (access.put state tape) = tape
  put_put : ∀ state first second, access.put (access.put state first) second = access.put state second

/-- Supplied heads work under arbitrary policy; the head itself proves that
the diagnostic cursor guard is not entered. -/
theorem perform_supplied {S : Type} (access : Access S) (state : S) (tape : Tape)
    (request : AddressRequest) (input : Input) (current : access.get state = tape)
    (head : tape.inputs[tape.cursor]? = some input) (support : Supported request input) :
    perform access request state = .ok input (access.put state (advance tape request input)) := by
  cases support with
  | index kind count value bound =>
    have actual := index_supplied_any_policy access state tape kind.site count value current head bound
    simp only [perform,bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl
  | bernoulli kind rate value validFalse probability allowed =>
    have actual := bernoulli_supplied_any_policy access state tape kind.site rate value validFalse current head probability allowed
    simp only [perform,bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl

theorem zero_supported {request : AddressRequest} {input : Input} (value : RawZeroValue request input) : Supported request input := by
  cases value with
  | index kind count positive => exact .index kind count 0 positive
  | bernoulliFalse kind rate allowed => exact .bernoulli kind rate false true allowed allowed
  | bernoulliTrue kind rate falseAllowed trueAllowed => exact .bernoulli kind rate true false falseAllowed trueAllowed

theorem done_environment (budget : Nat) (tape : Tape) : Environment (.done : Plan budget) tape := ⟨True.intro⟩

theorem halted_environment (budget : Nat) (reason : String) (tape : Tape) :
    Environment (.halted reason : Plan budget) tape := ⟨True.intro⟩

theorem fits_pad {budget : Nat} (plan : Plan budget) (tape : Tape) : Fits plan.pad tape ↔ Fits plan tape := by
  induction plan generalizing tape with
  | done => rfl
  | blocked => rfl
  | halted reason => rfl
  | request request next ih =>
    simp only [Plan.pad,Fits]
    constructor
    · rintro ⟨input,supported,after,step,tail⟩
      exact ⟨input,supported,after,step,(ih input supported after).mp tail⟩
    · rintro ⟨input,supported,after,step,tail⟩
      exact ⟨input,supported,after,step,(ih input supported after).mpr tail⟩

end EmptyFunction.PolicyChoiceSupply
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.PolicyChoiceSupply.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved policy supply axiom {dependency} in {name}"
