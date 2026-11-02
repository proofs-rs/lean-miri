import empty_function.MachineAddressPartial
import empty_function.ChoiceBernoulliPartial
import empty_function.ChoicePartial
namespace EmptyFunction.ManagedAddressTotal
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.MachineAddressPartial
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S
private theorem put_threads (state : S) (tape : ExecutionChoices.Tape) :
    (ChoiceExecution.tapeAccess.put state tape).threads = state.threads := rfl

private theorem index_continue {A : Type} (state : S) (site : ExecutionChoices.IndexSite) (count : Nat)
    (next : Nat → EStateM StepError S A)
    (post : ∀ value tape, value < count → NonUBResult (next value (ChoiceExecution.tapeAccess.put state tape))) :
    NonUBResult ((do let value ← ExecutionChoices.index ChoiceExecution.tapeAccess site count; next value) state) := by
  have result := ChoicePartial.index ChoiceExecution.tapeAccess state site count (by intros; rfl)
  cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess site count state with
  | error error after => simpa [actual,NonUBResult,bind,EStateM.bind] using result
  | ok value after =>
    simp only [actual] at result
    obtain ⟨within,tape,equal⟩ := result
    subst after
    simpa only [bind,EStateM.bind,actual] using post value tape within

private theorem bool_continue {A : Type} (state : S) (site : ExecutionChoices.BoolSite) (bits : UInt64)
    (next : Bool → EStateM StepError S A)
    (post : ∀ value tape, NonUBResult (next value (ChoiceExecution.tapeAccess.put state tape))) :
    NonUBResult ((do let value ← ExecutionChoices.bernoulli ChoiceExecution.tapeAccess site bits; next value) state) := by
  have result := ChoiceBernoulliPartial.bernoulli ChoiceExecution.tapeAccess state site bits (by intros; rfl)
  cases actual : ExecutionChoices.bernoulli ChoiceExecution.tapeAccess site bits state with
  | error error after => simpa [actual,NonUBResult,bind,EStateM.bind] using result
  | ok value after =>
    simp only [actual] at result
    obtain ⟨⟨tape,equal⟩,_⟩ := result
    subst after
    simpa only [bind,EStateM.bind,actual] using post value tape

theorem source_eq (access : ExecutionChoices.Access S) (h : ChoiceExecution.H)
    (id : AllocId) (kind : Option AddressMemoryKind) :
    MachineAddress.addrFromAllocId access h id kind = (do
      let initial := (← get).user.addresses
      if let some cached := initial.baseAddr.find? (fun entry => entry.allocId == id) then return cached.address
      let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
      let state ← get
      let info ← match state.memory.getAllocInfo id with
        | .ok info => pure info
        | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
      if info.kind == .dead || !state.memory.isAllocLive id then
        throw (h.classifyAddressError (.deadAllocation id))
      let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
      if info.kind == .typeId || initial.addressMode != .managed then
        return ← MachineAddress.assign h id (some kind) unused
      let some generation := initial.generation | throw (h.classifyAddressError .missingAddressGeneration)
      let reuse ← if kind == .stack then pure false else
        ExecutionChoices.bernoulli access .addressReuse generation.reusePool.addressReuseRate.toBits
      let cross ← if reuse then ExecutionChoices.bernoulli access .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
        else pure false
      let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
        (UInt32.ofNat (← get).threads.activeThread.toNat)
      modify fun (state : S) => {state with user := {state.user with addresses :=
        {initial with generation := some {generation with reusePool := prepared.state}}}}
      let range ← match prepared.outcome with
        | .ok range => pure range | .error error => throw (h.classifyAddressError (.reusePool error))
      let choices ← match range with
        | none => do
          let selected ← (do
            let selected ← ExecutionChoices.index access .addressSlack 16
            if valid : selected < 16 then pure (⟨selected,valid⟩ : Fin 16)
            else throw (StepError.invalidProgram "checked address slack exceeded support"))
          pure {unused with reuse, crossThread := cross, slack := selected}
        | some (begin,stop) => do
          let selected ← ExecutionChoices.index access .addressPool (stop-begin)
          pure {unused with reuse, crossThread := cross, poolIndex := begin+selected}
      MachineAddress.assign h id (some kind) choices) := rfl


private theorem choose_assign (h : ChoiceExecution.H) (state : S) (id : AllocId)
    (kind : AddressMemoryKind) (reuse cross : Bool) (range : Option (Nat × Nat))
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none)
    (classifier : h.classifyAddressError = PointerSource.addressError) :
    NonUBResult ((do
      let choices ← match range with
        | none => do
          let selected ← (do
            let value ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressSlack 16
            if valid : value < 16 then pure (⟨value,valid⟩ : Fin 16)
            else throw (StepError.invalidProgram "checked address slack exceeded support"))
          pure (⟨reuse,cross,0,selected⟩ : AddressRandomChoices)
        | some (begin,stop) => do
          let selected ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressPool (stop-begin)
          pure (⟨reuse,cross,begin+selected,⟨0,by decide⟩⟩ : AddressRandomChoices)
      MachineAddress.assign h id (some kind) choices : EStateM StepError S UInt64) state) := by
  cases range with
  | none =>
    have post := ChoicePartial.index ChoiceExecution.tapeAccess state .addressSlack 16 (by intros; rfl)
    cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess .addressSlack 16 state with
    | error error failed => simpa [actual,NonUBResult,bind,EStateM.bind] using post
    | ok value after =>
      simp only [actual] at post
      obtain ⟨within,tape,equal⟩ := post
      subst after
      simpa [actual,bind,EStateM.bind,pure,EStateM.pure,within] using
        MachineAddressPartial.assign h (ChoiceExecution.tapeAccess.put state tape) id (some kind)
          ⟨reuse,cross,0,⟨value,within⟩⟩ managed noRace classifier
  | some pair =>
    obtain ⟨begin,stop⟩ := pair
    have post := ChoicePartial.index ChoiceExecution.tapeAccess state .addressPool (stop-begin) (by intros; rfl)
    cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess .addressPool (stop-begin) state with
    | error error failed => simpa [actual,NonUBResult,bind,EStateM.bind] using post
    | ok value after =>
      simp only [actual] at post
      obtain ⟨within,tape,equal⟩ := post
      subst after
      simpa [actual,bind,EStateM.bind,pure,EStateM.pure] using
        MachineAddressPartial.assign h (ChoiceExecution.tapeAccess.put state tape) id (some kind)
          ⟨reuse,cross,begin+value,⟨0,by decide⟩⟩ managed noRace classifier

private theorem prepared_assign (h : ChoiceExecution.H) (state : S) (id : AllocId)
    (kind : AddressMemoryKind) (reuse cross : Bool) (initial : GlobalAddressState)
    (generation : AddressGenerationState) (prepared : ReusePoolResult (Option (Nat × Nat)))
    (managed : initial.addressMode = .managed) (noRace : state.dataRace = none)
    (classifier : h.classifyAddressError = PointerSource.addressError) :
    NonUBResult ((do
      modify fun (state : S) => {state with user := {state.user with addresses :=
        {initial with generation := some {generation with reusePool := prepared.state}}}}
      let range ← match prepared.outcome with
        | .ok range => pure range | .error error => throw (h.classifyAddressError (.reusePool error))
      let choices ← match range with
        | none => do
          let selected ← (do
            let value ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressSlack 16
            if valid : value < 16 then pure (⟨value,valid⟩ : Fin 16)
            else throw (StepError.invalidProgram "checked address slack exceeded support"))
          pure (⟨reuse,cross,0,selected⟩ : AddressRandomChoices)
        | some (begin,stop) => do
          let selected ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressPool (stop-begin)
          pure (⟨reuse,cross,begin+selected,⟨0,by decide⟩⟩ : AddressRandomChoices)
      MachineAddress.assign h id (some kind) choices : EStateM StepError S UInt64) state) := by
  cases outcome : prepared.outcome with
  | error error =>
    simp [outcome,classifier,NonUBResult,AddressErrorClass.address,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,
      throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  | ok range =>
    simpa [outcome,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
      bind,EStateM.bind,pure,EStateM.pure] using
      choose_assign h {state with user := {state.user with addresses :=
        {initial with generation := some {generation with reusePool := prepared.state}}}}
        id kind reuse cross range managed noRace classifier


private theorem generation_assign (h : ChoiceExecution.H) (state : S) (id : AllocId)
    (info : AllocationInfo) (kind : AddressMemoryKind) (generation : AddressGenerationState)
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none)
    (classifier : h.classifyAddressError = PointerSource.addressError) :
    NonUBResult ((do
      let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
      let reuse ← if kind == .stack then pure false else
        ExecutionChoices.bernoulli ChoiceExecution.tapeAccess .addressReuse generation.reusePool.addressReuseRate.toBits
      let cross ← if reuse then ExecutionChoices.bernoulli ChoiceExecution.tapeAccess .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
        else pure false
      let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
        (UInt32.ofNat (← get).threads.activeThread.toNat)
      modify fun (current : S) => {current with user := {current.user with addresses :=
        {state.user.addresses with generation := some {generation with reusePool := prepared.state}}}}
      let range ← match prepared.outcome with
        | .ok range => pure range | .error error => throw (h.classifyAddressError (.reusePool error))
      let choices ← match range with
        | none => do
          let selected ← (do
            let selected ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressSlack 16
            if valid : selected < 16 then pure (⟨selected,valid⟩ : Fin 16)
            else throw (StepError.invalidProgram "checked address slack exceeded support"))
          pure {unused with reuse, crossThread := cross, slack := selected}
        | some (begin,stop) => do
          let selected ← ExecutionChoices.index ChoiceExecution.tapeAccess .addressPool (stop-begin)
          pure {unused with reuse, crossThread := cross, poolIndex := begin+selected}
      MachineAddress.assign h id (some kind) choices : EStateM StepError S UInt64) state) := by
  by_cases stack : kind = .stack
  · subst kind
    simpa [put_threads,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using
      prepared_assign h state id .stack false false state.user.addresses generation
        (generation.reusePool.prepareTakeAddr false false info.size info.align .stack
          (UInt32.ofNat state.threads.activeThread.toNat)) managed noRace classifier
  · simp only [beq_iff_eq,stack,↓reduceIte]
    apply bool_continue
    intro reuse reuseTape
    cases reuse with
    | false =>
      simpa [put_threads,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using
        prepared_assign h (ChoiceExecution.tapeAccess.put state reuseTape) id kind false false state.user.addresses generation
          (generation.reusePool.prepareTakeAddr false false info.size info.align kind
            (UInt32.ofNat state.threads.activeThread.toNat)) managed noRace classifier
    | true =>
      apply bool_continue
      intro cross crossTape
      simpa [put_threads,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using
        prepared_assign h (ChoiceExecution.tapeAccess.put (ChoiceExecution.tapeAccess.put state reuseTape) crossTape)
          id kind true cross state.user.addresses generation
          (generation.reusePool.prepareTakeAddr true cross info.size info.align kind
            (UInt32.ofNat state.threads.activeThread.toNat)) managed noRace classifier


/-- Every error of the actual managed address action is non-UB, for arbitrary
tape contents, policies, seeds, pool layouts, generator capacity and cursor.
This theorem does not claim that malformed states or exhausted resources run
successfully. -/
theorem address (h : ChoiceExecution.H) (state : S) (id : AllocId)
    (kind : Option AddressMemoryKind)
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none)
    (classifier : h.classifyAddressError = PointerSource.addressError) :
    NonUBResult (MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess h id kind state) := by
  rw [source_eq]
  cases cache : state.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) with
  | some cached =>
    simp [cache,NonUBResult,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  | none =>
    cases kind with
    | none =>
      simp [cache,NonUBResult,classifier,AddressErrorClass.address,get,getThe,MonadStateOf.get,EStateM.get,
        bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | some kind =>
      cases metadata : state.memory.getAllocInfo id with
      | error error =>
        simp [cache,metadata,NonUBResult,AddressErrorClass.callback,get,getThe,MonadStateOf.get,EStateM.get,
          bind,EStateM.bind,throw,throwThe,MonadExceptOf.throw,EStateM.throw]
      | ok info =>
        by_cases dead : info.kind = .dead ∨ state.memory.isAllocLive id = false
        · simp [cache,metadata,dead,classifier,NonUBResult,AddressErrorClass.address,
            get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
            throw,throwThe,MonadExceptOf.throw,EStateM.throw]
        · have notDead := (not_or.mp dead).1
          have isLive := (not_or.mp dead).2
          by_cases typeId : info.kind = .typeId
          · simpa [cache,metadata,dead,notDead,isLive,typeId,managed,get,getThe,MonadStateOf.get,EStateM.get,
              bind,EStateM.bind,pure,EStateM.pure] using
              MachineAddressPartial.assign h state id (some kind) ⟨false,false,0,⟨0,by decide⟩⟩ managed noRace classifier
          · cases current : state.user.addresses.generation with
            | none =>
              simp [cache,metadata,dead,notDead,isLive,typeId,managed,current,classifier,NonUBResult,AddressErrorClass.address,
                get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
                throw,throwThe,MonadExceptOf.throw,EStateM.throw]
            | some generation =>
              simpa [cache,metadata,dead,notDead,isLive,typeId,managed,current,get,getThe,MonadStateOf.get,EStateM.get,
                bind,EStateM.bind,pure,EStateM.pure] using
                generation_assign h state id info kind generation managed noRace classifier
end EmptyFunction.ManagedAddressTotal
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ManagedAddressTotal.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved managed address total axiom {dependency} in {name}"
