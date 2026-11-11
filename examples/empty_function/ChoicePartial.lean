import empty_function.AddressErrorClass
import empty_function.RelocationByteActual
namespace EmptyFunction.ChoicePartial
open Miri Miri.Interpreter ExecutionChoices
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
private def unknownSource {S A : Type} (message : String) : EStateM StepError S A :=
  throw (.callback s!"choice input unknown: {message}")

/-- Definitionally exact source equations with public source wrappers. -/
private theorem demand_index_eq {S : Type} (access : Access S) (site : IndexSite) (count : Nat) :
    demandSource access (.index site count) = (do
      let tape := access.get (← get)
      if tape.cursor > tape.inputs.size then
        match tape.policy with
        | .strict => pure ()
        | .boundedDiagnostic _ _ | .boundedSeededDiagnostic _ _ _ | .diagnostic | .seededDiagnostic _ =>
          throw (.invalidProgram "diagnostic choice cursor exceeds supplied input prefix")
      if let some value := tape.inputs[tape.cursor]? then return value
      match tape.policy with
      | .strict => unknownSource "tape exhausted"
      | .boundedDiagnostic maxChoices maxByteLength => do
        if tape.generatedChoices >= maxChoices then
          throw (.resourceExhaustion "bounded diagnostic choice count exhausted")
        let value ← diagnosticInputSource (.index site count) maxByteLength
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1}
        return value
      | .boundedSeededDiagnostic maxChoices maxByteLength seed => do
        if tape.generatedChoices >= maxChoices then
          throw (.resourceExhaustion "bounded seeded diagnostic choice count exhausted")
        let (value,nextState) ← seededDiagnosticInputSource (.index site count) maxByteLength seed
          tape.diagnosticRngState (tape.generatedChoices == 0)
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1, diagnosticRngState := nextState}
        return value
      | .diagnostic => do
        let value ← diagnosticInputSource (.index site count) 0
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1}
        return value
      | .seededDiagnostic seed => do
        let (value,nextState) ← seededDiagnosticInputSource (.index site count) 0 seed
          tape.diagnosticRngState (tape.generatedChoices == 0)
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1, diagnosticRngState := nextState}
        return value) := rfl

private theorem index_eq {S : Type} (access : Access S) (site : IndexSite) (count : Nat) :
    ExecutionChoices.index access site count = (do
      if count == 0 then throw (.invalidProgram "source random selection has empty support")
      let request := Request.index site count
      let input ← demandSource access request
      let .index actual value := input | unknownSource s!"expected index at {repr site}"
      unless actual == site do unknownSource s!"index site mismatch at {repr site}"
      unless value < count do unknownSource s!"index outside support at {repr site}"
      modify fun state =>
        let tape := access.get state
        access.put state {tape with cursor := tape.cursor+1,events := tape.events.push ⟨request,input⟩}
      pure value) := rfl

private def DemandPost {S : Type} (access : Access S) (before : S)
    (result : EStateM.Result StepError S Input) : Prop :=
  match result with
  | .error error _ => RunLoop.reportsUB error = false
  | .ok _ after => after = before ∨ ∃ tape, after = access.put before tape

private theorem demand_index {S : Type} (access : Access S) (state : S)
    (site : IndexSite) (count : Nat) :
    DemandPost access state (demandSource access (.index site count) state) := by
  rw [demand_index_eq]
  simp only [diagnosticInputSource_index,seededDiagnosticInputSource_index,unknownSource]
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  cases policy : (access.get state).policy <;>
    cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
    simp only [policy,lookup] <;>
    repeat' first
      | (solve | simp [DemandPost,RunLoop.reportsUB,EStateM.pure,EStateM.bind,EStateM.throw,EStateM.modifyGet]; try (first | exact Or.inr ⟨_,rfl⟩ | exact ⟨_,rfl⟩ | assumption))
      | split


/-- Exact source choice behavior for arbitrary policies and tape contents.
Insufficient quota or malformed input stops with its actual non-UB error. -/
theorem index {S : Type} (access : Access S) (state : S) (site : IndexSite) (count : Nat)
    (putPut : ∀ (state : S) first second, access.put (access.put state first) second = access.put state second) :
    match ExecutionChoices.index access site count state with
    | .error error _ => RunLoop.reportsUB error = false
    | .ok value after => value < count ∧ ∃ tape, after = access.put state tape := by
  by_cases zero : count = 0
  · simp [index_eq,zero,unknownSource,throw,throwThe,MonadExceptOf.throw,EStateM.throw,
      bind,EStateM.bind,RunLoop.reportsUB]
  ·
    have post := demand_index access state site count
    cases actual : demandSource access (.index site count) state with
    | error error after =>
      simp only [actual,DemandPost] at post
      rw [index_eq]
      simp only [unknownSource]
      simp [zero,actual,post,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
        pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | ok input middle =>
      simp only [actual,DemandPost] at post
      have changed (tape : Tape) : ∃ next, access.put middle tape = access.put state next := by
        rcases post with equal | ⟨previous,equal⟩
        · exact ⟨tape,by rw [equal]⟩
        · exact ⟨tape,by rw [equal,putPut]⟩
      rw [index_eq]
      simp only [unknownSource]
      cases input <;>
        simp only [zero,beq_iff_eq,↓reduceIte,actual,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
          pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
      case index actualSite value =>
        by_cases same : actualSite = site <;> by_cases within : value < count <;>
          simp [same,within,RunLoop.reportsUB,EStateM.bind,EStateM.throw,EStateM.pure,EStateM.modifyGet]
        exact changed _
      all_goals simp [RunLoop.reportsUB,EStateM.bind,EStateM.throw,EStateM.pure]
end EmptyFunction.ChoicePartial
