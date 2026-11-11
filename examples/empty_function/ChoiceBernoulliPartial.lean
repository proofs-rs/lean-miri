import empty_function.AddressErrorClass
import empty_function.RelocationByteActual
namespace EmptyFunction.ChoiceBernoulliPartial
open Miri Miri.Interpreter ExecutionChoices
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
private def unknownSource {S A : Type} (message : String) : EStateM StepError S A :=
  throw (.callback s!"choice input unknown: {message}")

/-- Definitionally exact source equations with public source wrappers.
Index/Bernoulli draws never inspect the byte-length limit, so the bounded draw
wrapper with limit zero is also definitionally the uncapped draw here. No
choice-count or support constraint is added to the uncapped policy branches. -/
private theorem demand_bernoulli_eq {S : Type} (access : Access S) (site : BoolSite) (bits : UInt64) :
    demandSource access (.bernoulli site bits) = (do
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
        let value ← diagnosticInputSource (.bernoulli site bits) maxByteLength
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1}
        return value
      | .boundedSeededDiagnostic maxChoices maxByteLength seed => do
        if tape.generatedChoices >= maxChoices then
          throw (.resourceExhaustion "bounded seeded diagnostic choice count exhausted")
        let (value,nextState) ← seededDiagnosticInputSource (.bernoulli site bits) maxByteLength seed
          tape.diagnosticRngState (tape.generatedChoices == 0)
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1, diagnosticRngState := nextState}
        return value
      | .diagnostic => do
        let value ← diagnosticInputSource (.bernoulli site bits) 0
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1}
        return value
      | .seededDiagnostic seed => do
        let (value,nextState) ← seededDiagnosticInputSource (.bernoulli site bits) 0 seed
          tape.diagnosticRngState (tape.generatedChoices == 0)
        modify fun state =>
          let current := access.get state
          access.put state {current with inputs := current.inputs.push value, generatedChoices := current.generatedChoices+1, diagnosticRngState := nextState}
        return value) := rfl

private theorem permits (bits : UInt64) (choice : Bool) :
    match TerminatorMachine.permitsPreemption bits choice with
    | .ok _ => True
    | .error error => RunLoop.reportsUB error = false := by
  unfold TerminatorMachine.permitsPreemption
  cases decoded : (FloatBits.mk .binary64 (BitVec.ofNat 128 bits.toNat)).decode with
  | error error => simp [decoded,Except.mapError,bind,Except.bind,AddressErrorClass.invariant]
  | ok decodedValue =>
    cases value : decodedValue.value with
    | finite numerator denominator =>
      by_cases invalid : (denominator == 0 || numerator > denominator || (decodedValue.negative && numerator != 0)) = true <;>
        simp [decoded,value,invalid,Except.mapError,bind,Except.bind,pure,Except.pure,
          throw,throwThe,MonadExceptOf.throw,AddressErrorClass.invariant]
    | infinite => simp [decoded,value,Except.mapError,bind,Except.bind,pure,Except.pure,
        throw,throwThe,MonadExceptOf.throw,AddressErrorClass.invariant]
    | nan payload => simp [decoded,value,Except.mapError,bind,Except.bind,pure,Except.pure,
        throw,throwThe,MonadExceptOf.throw,AddressErrorClass.invariant]

private def DemandPost {S : Type} (access : Access S) (before : S)
    (result : EStateM.Result StepError S Input) : Prop :=
  match result with
  | .error error _ => RunLoop.reportsUB error = false
  | .ok _ after => after = before ∨ ∃ tape, after = access.put before tape

private def RawPost {S A : Type} (state : S) (result : EStateM.Result StepError S A) : Prop :=
  match result with
  | .error error _ => RunLoop.reportsUB error = false
  | .ok _ after => after = state

private theorem diagnostic {S : Type} (state : S) (site : BoolSite) (bits : UInt64) (maximum : Nat) :
    RawPost state (diagnosticInputSource (.bernoulli site bits) maximum state) := by
  have fp := permits bits false
  have tp := permits bits true
  rw [diagnosticInputSource_bernoulli]
  cases first : TerminatorMachine.permitsPreemption bits false with
  | error error => simpa [first,RawPost,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using fp
  | ok firstAllowed =>
    cases firstAllowed <;> cases second : TerminatorMachine.permitsPreemption bits true <;>
      simp only [first,second] at fp tp ⊢ <;>
      simp_all [RawPost,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.resource]
    all_goals
      rename_i allowed
      cases allowed <;> simp [RawPost,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.resource]

private theorem seeded {S : Type} (state : S) (site : BoolSite) (bits : UInt64) (maximum : Nat)
    (seed rng : UInt64) (firstGenerated : Bool) :
    RawPost state (seededDiagnosticInputSource (.bernoulli site bits) maximum seed rng firstGenerated state) := by
  have fp := permits bits false
  have tp := permits bits true
  rw [seededDiagnosticInputSource_bernoulli]
  cases first : TerminatorMachine.permitsPreemption bits false with
  | error error => simpa [first,RawPost,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using fp
  | ok firstAllowed =>
    cases second : TerminatorMachine.permitsPreemption bits true with
    | error error =>
      simp only [second] at tp
      simpa [first,second,RawPost,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using tp
    | ok secondAllowed =>
      cases firstAllowed <;> cases secondAllowed <;> cases firstGenerated <;>
        simp only [first,second,Bool.false_or,Bool.true_or,Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,
          ↓reduceIte,bind,EStateM.bind,pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
      all_goals repeat' first
        | (solve | simp [RawPost,AddressErrorClass.resource,AddressErrorClass.invariant,EStateM.bind,EStateM.pure,EStateM.throw])
        | split
      all_goals
        cases decoded : (FloatBits.mk .binary64 (BitVec.ofNat 128 bits.toNat)).decode with
        | error error => simp [decoded,RawPost,EStateM.bind,EStateM.throw,AddressErrorClass.invariant]
        | ok decodedValue =>
          cases value : decodedValue.value <;>
            simp [decoded,value,RawPost,EStateM.bind,EStateM.throw,EStateM.pure,AddressErrorClass.invariant]

theorem demand_bernoulli {S : Type} (access : Access S) (state : S)
    (site : BoolSite) (bits : UInt64) :
    DemandPost access state (demandSource access (.bernoulli site bits) state) := by
  cases policy : (access.get state).policy with
  | strict =>
    cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
      by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
      simp [demand_bernoulli_eq,policy,lookup,past,unknownSource,DemandPost,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.callback]
  | boundedDiagnostic quota maximum =>
    have raw := diagnostic state site bits maximum
    cases outcome : diagnosticInputSource (.bernoulli site bits) maximum state with
    | error error failed =>
      simp only [outcome,RawPost] at raw
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        by_cases full : (access.get state).generatedChoices ≥ quota <;>
        simp [demand_bernoulli_eq,policy,lookup,past,full,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.invariant,AddressErrorClass.resource,raw]
    | ok input middle =>
      simp only [outcome,RawPost] at raw
      subst middle
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        by_cases full : (access.get state).generatedChoices ≥ quota <;>
        simp [demand_bernoulli_eq,policy,lookup,past,full,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          AddressErrorClass.invariant,AddressErrorClass.resource] <;> exact Or.inr ⟨_,rfl⟩
  | boundedSeededDiagnostic quota maximum seed =>
    have raw := seeded state site bits maximum seed (access.get state).diagnosticRngState ((access.get state).generatedChoices == 0)
    cases outcome : seededDiagnosticInputSource (.bernoulli site bits) maximum seed
        (access.get state).diagnosticRngState ((access.get state).generatedChoices == 0) state with
    | error error failed =>
      simp only [outcome,RawPost] at raw
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        by_cases full : (access.get state).generatedChoices ≥ quota <;>
        simp [demand_bernoulli_eq,policy,lookup,past,full,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.invariant,AddressErrorClass.resource,raw]
    | ok input middle =>
      simp only [outcome,RawPost] at raw
      subst middle
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        by_cases full : (access.get state).generatedChoices ≥ quota <;>
        simp [demand_bernoulli_eq,policy,lookup,past,full,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          AddressErrorClass.invariant,AddressErrorClass.resource] <;> exact Or.inr ⟨_,rfl⟩
  | diagnostic =>
    have raw := diagnostic state site bits 0
    cases outcome : diagnosticInputSource (.bernoulli site bits) 0 state with
    | error error failed =>
      simp only [outcome,RawPost] at raw
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        simp [demand_bernoulli_eq,policy,lookup,past,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.invariant,AddressErrorClass.resource,raw]
    | ok input middle =>
      simp only [outcome,RawPost] at raw
      subst middle
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        simp [demand_bernoulli_eq,policy,lookup,past,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          AddressErrorClass.invariant,AddressErrorClass.resource] <;> exact Or.inr ⟨_,rfl⟩
  | seededDiagnostic seed =>
    have raw := seeded state site bits 0 seed (access.get state).diagnosticRngState ((access.get state).generatedChoices == 0)
    cases outcome : seededDiagnosticInputSource (.bernoulli site bits) 0 seed
        (access.get state).diagnosticRngState ((access.get state).generatedChoices == 0) state with
    | error error failed =>
      simp only [outcome,RawPost] at raw
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        simp [demand_bernoulli_eq,policy,lookup,past,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,AddressErrorClass.invariant,AddressErrorClass.resource,raw]
    | ok input middle =>
      simp only [outcome,RawPost] at raw
      subst middle
      cases lookup : (access.get state).inputs[(access.get state).cursor]? <;>
        by_cases past : (access.get state).cursor > (access.get state).inputs.size <;>
        simp [demand_bernoulli_eq,policy,lookup,past,outcome,DemandPost,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          throw,throwThe,MonadExceptOf.throw,EStateM.throw,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
          AddressErrorClass.invariant,AddressErrorClass.resource] <;> exact Or.inr ⟨_,rfl⟩

private theorem bernoulli_eq {S : Type} (access : Access S) (site : BoolSite) (bits : UInt64) :
    ExecutionChoices.bernoulli access site bits = (do
      let _ ← match TerminatorMachine.permitsPreemption bits false with
        | .ok permitted => pure permitted | .error error => throw error
      let request := Request.bernoulli site bits
      let input ← demandSource access request
      let .boolean actual value := input | unknownSource s!"expected probability outcome at {repr site}"
      unless actual == site do unknownSource s!"probability site mismatch at {repr site}"
      let allowed ← match TerminatorMachine.permitsPreemption bits value with
        | .ok allowed => pure allowed | .error error => throw error
      unless allowed do unknownSource s!"Boolean outside probability support at {repr site}"
      modify fun state =>
        let tape := access.get state
        access.put state {tape with cursor := tape.cursor+1,events := tape.events.push ⟨request,input⟩}
      pure value) := rfl

/-- Invalid probabilities, arbitrary seeds, exhausted quotas, and malformed
supplied choices retain their actual non-UB stop. Every successful choice
changes only the tape lens and satisfies the queried support. -/
theorem bernoulli {S : Type} (access : Access S) (state : S) (site : BoolSite) (bits : UInt64)
    (putPut : ∀ (state : S) first second, access.put (access.put state first) second = access.put state second) :
    match ExecutionChoices.bernoulli access site bits state with
    | .error error _ => RunLoop.reportsUB error = false
    | .ok value after => (∃ tape, after = access.put state tape) ∧
      TerminatorMachine.permitsPreemption bits value = .ok true := by
  have firstPost := permits bits false
  cases first : TerminatorMachine.permitsPreemption bits false with
  | error error =>
    simp only [first] at firstPost
    simpa [bernoulli_eq,first,bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw] using firstPost
  | ok firstAllowed =>
    have post := demand_bernoulli access state site bits
    cases actual : demandSource access (.bernoulli site bits) state with
    | error error after =>
      simp only [actual,DemandPost] at post
      simpa [bernoulli_eq,first,actual,bind,EStateM.bind,pure,EStateM.pure,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw] using post
    | ok input middle =>
      simp only [actual,DemandPost] at post
      have changed (tape : Tape) : ∃ next, access.put middle tape = access.put state next := by
        rcases post with equal | ⟨previous,equal⟩
        · exact ⟨tape,by rw [equal]⟩
        · exact ⟨tape,by rw [equal,putPut]⟩
      rw [bernoulli_eq]
      simp only [unknownSource]
      cases input <;>
        simp only [first,actual,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
          pure,EStateM.pure,throw,throwThe,MonadExceptOf.throw,EStateM.throw,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
      case boolean actualSite value =>
        by_cases same : actualSite = site
        · have valuePost := permits bits value
          cases allowed : TerminatorMachine.permitsPreemption bits value with
          | error error =>
            simp only [allowed] at valuePost
            simpa [same,beq_iff_eq,allowed,EStateM.bind,EStateM.throw,EStateM.pure] using valuePost
          | ok supported =>
            cases supported <;>
              simp [same,beq_iff_eq,allowed,AddressErrorClass.callback,EStateM.bind,EStateM.throw,EStateM.pure,EStateM.modifyGet]
            exact changed _
        · simp [same,beq_iff_eq,AddressErrorClass.callback,EStateM.bind,EStateM.throw,EStateM.pure]
      all_goals simp [AddressErrorClass.callback,EStateM.bind,EStateM.throw,EStateM.pure]
end EmptyFunction.ChoiceBernoulliPartial
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ChoiceBernoulliPartial.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved partial Bernoulli axiom {dependency} in {name}"
