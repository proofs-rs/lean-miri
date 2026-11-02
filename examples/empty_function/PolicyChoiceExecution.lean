import empty_function.PolicyChoiceSupply
import empty_function.DiagnosticChoiceSupport
namespace EmptyFunction.PolicyChoiceExecution
open Miri Miri.ABI Miri.Memory Miri.Interpreter ExecutionChoices
open EmptyFunction.ChoiceSupply EmptyFunction.PolicyChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

theorem demand_zero {S : Type} (access : Access S) (state : S) (tape : Tape)
    (request : AddressRequest) (input : Input) (maximum bytes : Nat)
    (current : access.get state = tape) (policy : tape.policy = .boundedDiagnostic maximum bytes)
    (cursor : tape.cursor = tape.inputs.size) (quota : tape.generatedChoices < maximum)
    (value : RawZeroValue request input) :
    demandSource access (sourceRequest request) state = .ok input (access.put state (generated tape input)) := by
  have source := DiagnosticChoiceSupport.zero_helper state bytes value
  have notPast : ¬tape.cursor > tape.inputs.size := by omega
  have missing : tape.inputs[tape.cursor]? = none := by rw [cursor];exact Array.getElem?_size ..
  simp [demandSource_eq,current,policy,notPast,missing,show ¬tape.generatedChoices ≥ maximum from by omega,
    source,generated,get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,EStateM.bind,pure,EStateM.pure]

theorem demand_seeded {S : Type} (access : Access S) (state : S) (tape : Tape)
    (request : AddressRequest) (input : Input) (maximum bytes : Nat) (seed word nextRng : UInt64)
    (current : access.get state = tape) (policy : tape.policy = .boundedSeededDiagnostic maximum bytes seed)
    (cursor : tape.cursor = tape.inputs.size) (quota : tape.generatedChoices < maximum)
    (mix : nextDiagnosticWordSource (if tape.generatedChoices == 0 then seed else tape.diagnosticRngState) = (word,nextRng))
    (value : RawSeedValue request word input) :
    demandSource access (sourceRequest request) state = .ok input (access.put state (seeded tape input nextRng)) := by
  have source := DiagnosticChoiceSupport.seed_helper state bytes seed tape.diagnosticRngState
    (tape.generatedChoices == 0) word nextRng mix value
  have notPast : ¬tape.cursor > tape.inputs.size := by omega
  have missing : tape.inputs[tape.cursor]? = none := by rw [cursor];exact Array.getElem?_size ..
  simp [demandSource_eq,current,policy,notPast,missing,show ¬tape.generatedChoices ≥ maximum from by omega,
    source,seeded,generated,get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    bind,EStateM.bind,pure,EStateM.pure]

private theorem perform_from_demand {S : Type} (access : Access S) (state middle : S) (tape : Tape)
    (request : AddressRequest) (input : Input) (support : Supported request input)
    (source : demandSource access (sourceRequest request) state = .ok input middle)
    (current : access.get middle = tape) :
    perform access request state = .ok input (access.put middle (advance tape request input)) := by
  cases support with
  | index kind count value bound =>
    have actual := index_from_demand access state middle tape kind.site count value source current bound
    simp only [perform,bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl
  | bernoulli kind rate value validFalse probability allowed =>
    have actual := bernoulli_from_demand access state middle tape kind.site rate value validFalse source current probability allowed
    simp only [perform,bind,EStateM.bind,actual,pure,EStateM.pure]
    rfl

/-- The exact existing index/Bernoulli consumers implement every raw policy
step. Lens laws only combine generation and consumption's two actual writes. -/
theorem perform_policyStep {S : Type} (access : Access S) (laws : AccessLaws access)
    (state : S) (before after : Tape) (request : AddressRequest) (input : Input)
    (current : access.get state = before) (support : Supported request input)
    (step : PolicyStep request before input after) :
    perform access request state = .ok input (access.put state after) := by
  cases step with
  | supplied head => exact perform_supplied access state before request input current head support
  | diagnostic maximum bytes policy cursor quota value =>
    have source := demand_zero access state before request input maximum bytes current policy cursor quota value
    have actual := perform_from_demand access state (access.put state (generated before input))
      (generated before input) request input support source (laws.get_put ..)
    simpa only [laws.put_put] using actual
  | diagnosticSeeded maximum bytes seed word nextRng policy cursor quota mix value =>
    have source := demand_seeded access state before request input maximum bytes seed word nextRng current policy cursor quota mix value
    have actual := perform_from_demand access state (access.put state (seeded before input nextRng))
      (seeded before input nextRng) request input support source (laws.get_put ..)
    simpa only [laws.put_put] using actual
/-- Nat-valued form used by the source stack-address consumer. -/
theorem index_policyStep {S : Type} (access : Access S) (laws : AccessLaws access)
    (state : S) (before after : Tape) (kind : IndexKind) (count value : Nat)
    (current : access.get state = before) (bound : value < count)
    (step : PolicyStep (.index kind count) before (.index kind.site value) after) :
    ExecutionChoices.index access kind.site count state = .ok value (access.put state after) := by
  have actual := perform_policyStep access laws state before after (.index kind count) (.index kind.site value)
    current (.index kind count value bound) step
  cases outcome : ExecutionChoices.index access kind.site count state with
  | error error final =>
    simp only [perform,outcome,bind,EStateM.bind] at actual
    cases actual
  | ok selected final =>
    simp only [perform,outcome,bind,EStateM.bind,pure,EStateM.pure,EStateM.Result.ok.injEq,Input.index.injEq,true_and] at actual
    obtain ⟨same,states⟩ := actual
    subst selected
    rw [states]

theorem bernoulli_policyStep {S : Type} (access : Access S) (laws : AccessLaws access)
    (state : S) (before after : Tape) (kind : BoolKind) (rate : UInt64) (value : Bool)
    (current : access.get state = before) (support : Supported (.bernoulli kind rate) (.boolean kind.site value))
    (step : PolicyStep (.bernoulli kind rate) before (.boolean kind.site value) after) :
    ExecutionChoices.bernoulli access kind.site rate state = .ok value (access.put state after) := by
  have actual := perform_policyStep access laws state before after (.bernoulli kind rate) (.boolean kind.site value)
    current support step
  cases outcome : ExecutionChoices.bernoulli access kind.site rate state with
  | error error final =>
    simp only [perform,outcome,bind,EStateM.bind] at actual
    cases actual
  | ok selected final =>
    simp only [perform,outcome,bind,EStateM.bind,pure,EStateM.pure,EStateM.Result.ok.injEq,Input.boolean.injEq,true_and] at actual
    obtain ⟨same,states⟩ := actual
    subst selected
    rw [states]

end EmptyFunction.PolicyChoiceExecution
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.PolicyChoiceExecution.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved policy execution axiom {dependency} in {name}"
