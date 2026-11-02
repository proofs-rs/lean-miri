import empty_function.ManagedAddressTotal
import empty_function.ManagedAddressFrame
import empty_function.AddressAssignedSuccessPost
import empty_function.PrepareGenerationPost
import empty_function.AddressTransport
import empty_function.RelocationPost
import empty_function.RelocationTypeId
import empty_function.AddressBasePost
import empty_function.AddressStaticPost
namespace EmptyFunction.ManagedAddressRepresentation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
abbrev S := ChoiceExecution.S
private theorem put_addresses (state : S) (tape : ExecutionChoices.Tape) :
    (ChoiceExecution.tapeAccess.put state tape).user.addresses = state.user.addresses := rfl
private theorem put_threads (state : S) (tape : ExecutionChoices.Tape) :
    (ChoiceExecution.tapeAccess.put state tape).threads = state.threads := rfl

def Post (before : WholeCall.State) (after : S) : Prop :=
  (∃ generation, InputDraft.GenerationRepresentation {before with machine := after} generation) ∧
  (∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    after.user.addresses.baseAddr.find? (fun current => current.allocId == id) = some row) ∧
  AddressStaticPost.view after.user.addresses = AddressStaticPost.view before.machine.user.addresses

def ResultPost {A : Type} (before : WholeCall.State) (result : EStateM.Result StepError S A) : Prop :=
  match result with
  | .error _ _ => True
  | .ok _ after => Post before after

private theorem tape_rep (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation) (tape : ExecutionChoices.Tape) :
    InputDraft.GenerationRepresentation {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} generation :=
  AddressTransport.representation before {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} rfl rfl generation current

private theorem assign (h : ChoiceExecution.H) (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (choices : AddressRandomChoices)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true)
    (notDead : target.kind ≠ .dead) (notType : target.kind ≠ .typeId)
    (alignment : InputDraft.AlignmentRepresentation target.align)
    (noRace : before.machine.dataRace = none) :
    ResultPost before (MachineAddress.assign h id (some .other) choices before.machine) := by
  cases actual : MachineAddress.assign h id (some .other) choices before.machine with
  | error error failed => trivial
  | ok value after =>
    have pureActual := RelocationPost.assignment_state h before.machine id target choices
      missing metadata notDead notType live current.managed noRace value after actual
    have normalizedActual : AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
        (some ⟨if target.kind == .typeId then .typeId else .liveData,true,target.size,target.align,some .other,
          UInt32.ofNat before.machine.threads.activeThread.toNat⟩) choices) = .ok after.user.addresses := by
      simpa only [notType,beq_iff_eq,↓reduceIte] using pureActual
    obtain ⟨next,nextRep⟩ := AddressAssignedSuccessPost.assigned before generation current id target
      (UInt32.ofNat before.machine.threads.activeThread.toNat) choices after.user.addresses
      backing live metadata (fun _ _ => alignment) normalizedActual
    obtain ⟨addresses,frame⟩ := MachineAddressPartial.shape h before.machine id (some .other) choices current.managed noRace
    simp only [actual,MachineAddress.resultState] at frame
    have memoryEq : after.memory = before.machine.memory := by rw [frame]
    refine ⟨⟨next,AddressTransport.representation (AddressPost.withAddresses before after.user.addresses)
      {before with machine := after} memoryEq rfl next nextRep⟩,?_,?_⟩
    · exact AddressBasePost.retained _ id _ choices _ pureActual
    · exact AddressStaticPost.assignment _ id _ choices _ pureActual

private theorem index_continue {A : Type} (anchor : WholeCall.State) (state : S)
    (site : ExecutionChoices.IndexSite) (count : Nat) (next : Nat → EStateM StepError S A)
    (post : ∀ value tape, value < count → ResultPost anchor (next value (ChoiceExecution.tapeAccess.put state tape))) :
    ResultPost anchor ((do let value ← ExecutionChoices.index ChoiceExecution.tapeAccess site count; next value) state) := by
  have result := ChoicePartial.index ChoiceExecution.tapeAccess state site count (by intros; rfl)
  cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess site count state with
  | error error after => simp [actual,ResultPost,bind,EStateM.bind]
  | ok value after =>
    simp only [actual] at result
    obtain ⟨within,tape,equal⟩ := result
    subst after
    simpa only [bind,EStateM.bind,actual] using post value tape within

private theorem bool_continue {A : Type} (anchor : WholeCall.State) (state : S)
    (site : ExecutionChoices.BoolSite) (bits : UInt64) (next : Bool → EStateM StepError S A)
    (post : ∀ value tape, ResultPost anchor (next value (ChoiceExecution.tapeAccess.put state tape))) :
    ResultPost anchor ((do let value ← ExecutionChoices.bernoulli ChoiceExecution.tapeAccess site bits; next value) state) := by
  have result := ChoiceBernoulliPartial.bernoulli ChoiceExecution.tapeAccess state site bits (by intros; rfl)
  cases actual : ExecutionChoices.bernoulli ChoiceExecution.tapeAccess site bits state with
  | error error after => simp [actual,ResultPost,bind,EStateM.bind]
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





private theorem choose_assign (h : ChoiceExecution.H) (before : WholeCall.State)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (reuse cross : Bool) (range : Option (Nat × Nat))
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id) (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead) (notType : target.kind ≠ .typeId)
    (alignment : InputDraft.AlignmentRepresentation target.align) (noRace : before.machine.dataRace = none) :
    ResultPost before ((do
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
      MachineAddress.assign h id (some .other) choices : EStateM StepError S UInt64) before.machine) := by
  cases range with
  | none =>
    have post := ChoicePartial.index ChoiceExecution.tapeAccess before.machine .addressSlack 16 (by intros; rfl)
    cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess .addressSlack 16 before.machine with
    | error error failed => simp [actual,ResultPost,bind,EStateM.bind]
    | ok value after =>
      simp only [actual] at post
      obtain ⟨within,tape,equal⟩ := post
      subst after
      simpa [put_addresses,put_threads,ResultPost,Post,AddressStaticPost.view,actual,bind,EStateM.bind,pure,EStateM.pure,within,↓reduceDIte] using
        assign h {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} generation
          (tape_rep before generation current tape) id target ⟨reuse,cross,0,⟨value,within⟩⟩ missing
          (AddressTransport.backing before {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} rfl id backing) metadata live notDead notType alignment noRace
  | some pair =>
    obtain ⟨begin,stop⟩ := pair
    have post := ChoicePartial.index ChoiceExecution.tapeAccess before.machine .addressPool (stop-begin) (by intros; rfl)
    cases actual : ExecutionChoices.index ChoiceExecution.tapeAccess .addressPool (stop-begin) before.machine with
    | error error failed => simp [actual,ResultPost,bind,EStateM.bind]
    | ok value after =>
      simp only [actual] at post
      obtain ⟨within,tape,equal⟩ := post
      subst after
      simpa [put_addresses,put_threads,ResultPost,Post,AddressStaticPost.view,actual,bind,EStateM.bind,pure,EStateM.pure] using
        assign h {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} generation
          (tape_rep before generation current tape) id target ⟨reuse,cross,begin+value,⟨0,by decide⟩⟩ missing
          (AddressTransport.backing before {before with machine := ChoiceExecution.tapeAccess.put before.machine tape} rfl id backing) metadata live notDead notType alignment noRace


private theorem prepared_assign (h : ChoiceExecution.H) (before : WholeCall.State)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (reuse cross : Bool) (prepared : ReusePoolResult (Option (Nat × Nat)))
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id) (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead) (notType : target.kind ≠ .typeId)
    (alignment : InputDraft.AlignmentRepresentation target.align) (noRace : before.machine.dataRace = none)
    (actual : generation.reusePool.prepareTakeAddr reuse cross target.size target.align .other
      (UInt32.ofNat before.machine.threads.activeThread.toNat) = prepared) :
    ResultPost before ((do
      modify fun (state : S) => {state with user := {state.user with addresses :=
        {before.machine.user.addresses with generation := some {generation with reusePool := prepared.state}}}}
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
      MachineAddress.assign h id (some .other) choices : EStateM StepError S UInt64) before.machine) := by
  obtain ⟨bytes,bytesEq,normalized⟩ := alignment
  cases prepared with
  | mk pool outcome =>
    have preparedRep := PrepareGenerationPost.representation before generation current pool target.size target.align bytes
      (UInt32.ofNat before.machine.threads.activeThread.toNat) reuse cross bytesEq normalized outcome actual
    cases outcome with
    | error error =>
      simp [ResultPost,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,
        throw,throwThe,MonadExceptOf.throw,EStateM.throw]
    | ok range =>
      let stage := AddressPost.withAddresses before {before.machine.user.addresses with
        generation := some {generation with reusePool := pool}}
      have chosen := choose_assign h stage {generation with reusePool := pool} preparedRep id target reuse cross range
        missing (AddressTransport.backing before stage rfl id backing) metadata live notDead notType
        ⟨bytes,bytesEq,normalized⟩ noRace
      simpa [put_addresses,put_threads,ResultPost,Post,AddressStaticPost.view,stage,AddressPost.withAddresses,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
        bind,EStateM.bind,pure,EStateM.pure] using chosen


private theorem generation_assign (h : ChoiceExecution.H) (before : WholeCall.State)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id) (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead) (notType : target.kind ≠ .typeId)
    (alignment : InputDraft.AlignmentRepresentation target.align) (noRace : before.machine.dataRace = none) :
    ResultPost before ((do
      let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
      let reuse ← if (.other : AddressMemoryKind) == .stack then pure false else
        ExecutionChoices.bernoulli ChoiceExecution.tapeAccess .addressReuse generation.reusePool.addressReuseRate.toBits
      let cross ← if reuse then ExecutionChoices.bernoulli ChoiceExecution.tapeAccess .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits
        else pure false
      let prepared := generation.reusePool.prepareTakeAddr reuse cross target.size target.align (.other : AddressMemoryKind)
        (UInt32.ofNat (← get).threads.activeThread.toNat)
      modify fun (current : S) => {current with user := {current.user with addresses :=
        {before.machine.user.addresses with generation := some {generation with reusePool := prepared.state}}}}
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
      MachineAddress.assign h id (some (.other : AddressMemoryKind)) choices : EStateM StepError S UInt64) before.machine) := by
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,Bool.false_eq_true,↓reduceIte]
  apply bool_continue
  intro reuse reuseTape
  cases reuse with
  | false =>
    simpa [put_addresses,put_threads,ResultPost,Post,AddressStaticPost.view,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using
      prepared_assign h {before with machine := ChoiceExecution.tapeAccess.put before.machine reuseTape}
        generation (tape_rep before generation current reuseTape) id target false false
        (generation.reusePool.prepareTakeAddr false false target.size target.align .other
          (UInt32.ofNat before.machine.threads.activeThread.toNat)) missing
        (AddressTransport.backing before {before with machine := ChoiceExecution.tapeAccess.put before.machine reuseTape} rfl id backing)
        metadata live notDead notType alignment noRace rfl
  | true =>
    apply bool_continue
    intro cross crossTape
    let first := {before with machine := ChoiceExecution.tapeAccess.put before.machine reuseTape}
    let second := {first with machine := ChoiceExecution.tapeAccess.put first.machine crossTape}
    have secondRep := tape_rep first generation (tape_rep before generation current reuseTape) crossTape
    have chosen := prepared_assign h second generation secondRep id target true cross
      (generation.reusePool.prepareTakeAddr true cross target.size target.align .other
        (UInt32.ofNat before.machine.threads.activeThread.toNat)) missing
      (AddressTransport.backing before second rfl id backing) metadata live notDead notType alignment noRace rfl
    simpa [put_addresses,put_threads,ResultPost,Post,AddressStaticPost.view,first,second,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using chosen


/-- Successful actual address execution preserves full current geometry and
all previous address observations. Failed executions have no continuation
obligation; their non-UB classification is proved separately. -/
theorem address (h : ChoiceExecution.H) (before : WholeCall.State)
    (generation : AddressGenerationState) (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo)
    (backing : InputDraft.MetadataBacking before id) (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (live : before.machine.memory.isAllocLive id = true) (notDead : target.kind ≠ .dead)
    (alignment : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none →
      target.kind ≠ .typeId → InputDraft.AlignmentRepresentation target.align)
    (noRace : before.machine.dataRace = none) :
    ResultPost before (MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess h id (some .other) before.machine) := by
  cases cache : before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) with
  | some row =>
    rw [source_eq]
    simp only [cache,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
    exact ⟨⟨generation,current⟩,(by intro id row prior;exact prior),rfl⟩
  | none =>
    by_cases typeId : target.kind = .typeId
    · have actual := RelocationTypeId.address h before.machine id target cache metadata typeId live
      rw [actual]
      have zero := AddressPost.cache_zero before.machine.user.addresses id cache
      have rep := AddressPost.cache_zero_representation before generation current id cache
      rw [zero] at rep
      refine ⟨⟨generation,?_⟩,?_,rfl⟩
      · simpa only [AddressPost.withAddresses] using rep
      · intro oldId old prior
        simp only [Array.find?_push,prior,Option.or]
    · rw [source_eq]
      simpa [cache,metadata,live,notDead,typeId,current.managed,current.current,
        get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using
        generation_assign h before generation current id target cache backing metadata live notDead typeId
          (alignment cache typeId) noRace
end EmptyFunction.ManagedAddressRepresentation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ManagedAddressRepresentation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved managed address representation axiom {dependency} in {name}"
