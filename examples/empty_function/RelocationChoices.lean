import empty_function.RelocationContext
import empty_function.BumpAddress
import empty_function.RelocationAddress
import empty_function.RawResources
import empty_function.RelocationPost
namespace EmptyFunction.RelocationChoices
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev S := ChoiceExecution.S
abbrev H := ChoiceExecution.H
abbrev tapeAccess := ChoiceExecution.tapeAccess

def after (state : S) (request : AddressRequest) (input : ExecutionChoices.Input) : S :=
  tapeAccess.put state (advance (tapeAccess.get state) request input)

theorem get_after (state : S) (request : AddressRequest) (input : ExecutionChoices.Input) :
    tapeAccess.get (after state request input) = advance (tapeAccess.get state) request input := rfl

open Lean Elab Tactic in
elab "unfold_relocation_choice_helpers" : tactic => do
  for suffix in [".MachineAddress.rate", ".MachineAddress.slack", ".MachineAddress.setAddresses"] do
    let found := (←getEnv).constants.toList.filterMap fun (name,_) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := found | throwError "expected source helper {suffix}"
    evalTactic (← `(tactic| unfold $(mkIdent name)))

/-- Exact source two-draw no-reuse prefix. The continuation is the real assign
and its outcome is retained; typed tape support does not claim it succeeds. -/
theorem no_reuse_supplied (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState) (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (strict : (tapeAccess.get state).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse false))
    (head : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor]? = some (.boolean .addressReuse false))
    (next : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+1]? = some (.index .addressSlack value))
    (bound : value < 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true) :
    MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) state =
      MachineAddress.assign hooks id (some .other) ⟨false,false,0,⟨value,bound⟩⟩
        (after (after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
          (.boolean .addressReuse false)) (.index .slack 16) (.index .addressSlack value)) := by
  cases reuse with
  | bernoulli _ _ _ validFalse probability support =>
    have first := ExecutionChoices.bernoulli_supplied tapeAccess state (tapeAccess.get state)
      .addressReuse generation.reusePool.addressReuseRate.toBits false validFalse rfl strict head probability support
    let middle := after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse false)
    have second := ExecutionChoices.index_supplied tapeAccess middle (tapeAccess.get middle)
      .addressSlack 16 value rfl strict next bound
    have prepared := (ReuseTake.no_reuse generation.reusePool info.size info.align
      (UInt32.ofNat state.threads.activeThread.toNat) false 0 allowed).1
    unfold MachineAddress.addrFromAllocId
    unfold_relocation_choice_helpers
    simp [missing,metadata,notDead,notType,live,managed,current,first,
      get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
      MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure]
    have threadPreserve (tape : ExecutionChoices.Tape) :
      (tapeAccess.put state tape).threads = state.threads := rfl
    simp only [threadPreserve,prepared,EStateM.bind,EStateM.pure]
    simp only [←current,←managed]
    generalize sampled : ExecutionChoices.index tapeAccess .addressSlack 16 _ = result
    change ExecutionChoices.index tapeAccess .addressSlack 16 middle = result at sampled
    rw [second] at sampled
    cases sampled
    simp only [bound,↓reduceDIte]
    rfl
/-- Exact three-draw existing-hole prefix. All relative indices in the real
computed candidate interval are admitted. Pool/cache safety is proved separately. -/
theorem reuse_pool_supplied (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState)
    (bucket : Array ReusableAddress) (bytes : UInt64) (cross : Bool) (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (abiBytes : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (strict : (tapeAccess.get state).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor]? = some (.boolean .addressReuse true))
    (next : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+1]? = some (.boolean .addressCrossThread cross))
    (last : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+2]? = some (.index .addressPool value))
    (bound : value < (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).2 -
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).1)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross = true) :
    MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) state =
      MachineAddress.assign hooks id (some .other)
        ⟨true,cross,(ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).1+value,⟨0,by decide⟩⟩
        (after (after (after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
          (.boolean .addressReuse true)) (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
          (.boolean .addressCrossThread cross))
          (.index .pool ((ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).2 -
            (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).1))
          (.index .addressPool value)) := by
  cases reuse with
  | bernoulli _ _ _ validFalse probability support =>
    cases crossSupport with
    | bernoulli _ _ _ crossValid crossProbability crossSupported =>
      have first := ExecutionChoices.bernoulli_supplied tapeAccess state (tapeAccess.get state)
        .addressReuse generation.reusePool.addressReuseRate.toBits true validFalse rfl strict head probability support
      let one := after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true)
      have second := ExecutionChoices.bernoulli_supplied tapeAccess one (tapeAccess.get one)
        .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits cross crossValid
        rfl strict next crossProbability crossSupported
      let two := after one (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
        (.boolean .addressCrossThread cross)
      let range := ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross
      have lastAt : (tapeAccess.get two).inputs[(tapeAccess.get two).cursor]? = some (.index .addressPool value) := by
        simpa only [two,one,get_after,advance,Nat.add_assoc] using last
      have third := ExecutionChoices.index_supplied tapeAccess two (tapeAccess.get two)
        .addressPool (range.2-range.1) value rfl strict lastAt bound
      have nonempty : range.2 ≠ range.1 := by change value < range.2-range.1 at bound; omega
      have prepared := ReuseTake.prepare_bucket generation.reusePool bucket info.size info.align bytes
        (UInt32.ofNat state.threads.activeThread.toNat) cross present abiBytes normalized reuseAllowed crossAllowed
      change generation.reusePool.prepareTakeAddr true cross info.size info.align .other
        (UInt32.ofNat state.threads.activeThread.toNat) = ⟨generation.reusePool,.ok (if range.2 == range.1 then none else some range)⟩ at prepared
      simp only [show (range.2 == range.1) = false from by simpa using nonempty,Bool.false_eq_true,↓reduceIte] at prepared
      unfold MachineAddress.addrFromAllocId
      unfold_relocation_choice_helpers
      simp [missing,metadata,notDead,notType,live,managed,current,first,
        get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
        MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure]
      generalize crossed : ExecutionChoices.bernoulli tapeAccess .addressCrossThread
        generation.reusePool.addressReuseCrossThreadRate.toBits _ = crossResult
      change ExecutionChoices.bernoulli tapeAccess .addressCrossThread
        generation.reusePool.addressReuseCrossThreadRate.toBits one = crossResult at crossed
      rw [second] at crossed
      cases crossed
      have threadPreserve (s : S) (tape : ExecutionChoices.Tape) :
        (tapeAccess.put s tape).threads = s.threads := rfl
      have oneThreads : one.threads = state.threads := rfl
      simp only [threadPreserve,oneThreads,prepared,EStateM.bind,EStateM.pure]
      simp only [←current,←managed]
      generalize sampled : ExecutionChoices.index tapeAccess .addressPool (range.2-range.1) _ = result
      change ExecutionChoices.index tapeAccess .addressPool (range.2-range.1) two = result at sampled
      rw [third] at sampled
      cases sampled
      rfl

def staged (state : S) (initial : GlobalAddressState) (generation : AddressGenerationState)
    (pool : ReusePool) : S :=
  {state with user := {state.user with addresses := {initial with generation := some {generation with reusePool := pool}}}}

/-- Internal exact source adapter for the empty-pool branch. The successful
prepare equation is derived from arbitrary current pool data in ReuseEnsure.prepare. -/
private theorem reuse_empty_supplied_core (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState)
    (pool : ReusePool) (cross : Bool) (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (strict : (tapeAccess.get state).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor]? = some (.boolean .addressReuse true))
    (next : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+1]? = some (.boolean .addressCrossThread cross))
    (last : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+2]? = some (.index .addressSlack value))
    (bound : value < 16)
    (prepared : generation.reusePool.prepareTakeAddr true cross info.size info.align .other
      (UInt32.ofNat state.threads.activeThread.toNat) = ⟨pool,.ok none⟩) :
    MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) state =
      MachineAddress.assign hooks id (some .other) ⟨true,cross,0,⟨value,bound⟩⟩
        (after (staged
          (after (after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
            (.boolean .addressReuse true)) (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
            (.boolean .addressCrossThread cross)) state.user.addresses generation pool)
          (.index .slack 16) (.index .addressSlack value)) := by
  cases reuse with
  | bernoulli _ _ _ validFalse probability support =>
    cases crossSupport with
    | bernoulli _ _ _ crossValid crossProbability crossSupported =>
      have first := ExecutionChoices.bernoulli_supplied tapeAccess state (tapeAccess.get state)
        .addressReuse generation.reusePool.addressReuseRate.toBits true validFalse rfl strict head probability support
      let one := after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true)
      have second := ExecutionChoices.bernoulli_supplied tapeAccess one (tapeAccess.get one)
        .addressCrossThread generation.reusePool.addressReuseCrossThreadRate.toBits cross crossValid
        rfl strict next crossProbability crossSupported
      let two := after one (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
        (.boolean .addressCrossThread cross)
      let middle := staged two state.user.addresses generation pool
      have lastAt : (tapeAccess.get middle).inputs[(tapeAccess.get middle).cursor]? = some (.index .addressSlack value) := by
        change (tapeAccess.get two).inputs[(tapeAccess.get two).cursor]? = _
        simpa only [two,one,get_after,advance,Nat.add_assoc] using last
      have third := ExecutionChoices.index_supplied tapeAccess middle (tapeAccess.get middle)
        .addressSlack 16 value rfl strict lastAt bound
      unfold MachineAddress.addrFromAllocId
      unfold_relocation_choice_helpers
      simp [missing,metadata,notDead,notType,live,managed,current,first,
        get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
        MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure]
      generalize crossed : ExecutionChoices.bernoulli tapeAccess .addressCrossThread
        generation.reusePool.addressReuseCrossThreadRate.toBits _ = crossResult
      change ExecutionChoices.bernoulli tapeAccess .addressCrossThread
        generation.reusePool.addressReuseCrossThreadRate.toBits one = crossResult at crossed
      rw [second] at crossed
      cases crossed
      have threadPreserve (s : S) (tape : ExecutionChoices.Tape) :
        (tapeAccess.put s tape).threads = s.threads := rfl
      have oneThreads : one.threads = state.threads := rfl
      simp only [threadPreserve,oneThreads,prepared,EStateM.bind,EStateM.pure]
      simp only [←managed]
      generalize sampled : ExecutionChoices.index tapeAccess .addressSlack 16 _ = result
      change ExecutionChoices.index tapeAccess .addressSlack 16 middle = result at sampled
      rw [third] at sampled
      cases sampled
      simp only [bound,↓reduceDIte]
      rfl
/-- Full actual no-reuse address call from raw current representation and
both legal raw tape entries. No address/prepare/assign success is assumed. -/
theorem no_reuse_success (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : H) (id : AllocId) (info : AllocationInfo) (value : Nat)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive id = true)
    (strict : (tapeAccess.get before.machine).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse false))
    (head : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor]? = some (.boolean .addressReuse false))
    (next : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor+1]? = some (.index .addressSlack value))
    (bound : value < 16)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (room : RawGenerator.Room generation.generator info.size info.align ⟨value,bound⟩)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ final, MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) before.machine =
      .ok (RawGenerator.base generation.generator info.align ⟨value,bound⟩) final ∧
      tapeAccess.get final = advance
        (advance (tapeAccess.get before.machine) (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
          (.boolean .addressReuse false)) (.index .slack 16) (.index .addressSlack value) ∧
      final.memory = before.machine.memory ∧ final.borrowTracker = before.machine.borrowTracker ∧
      final.threads = before.machine.threads := by
  have allowed := ChoiceFloatSupport.allowed_of_supported .reuse _ false
    representation.reuseRateLower representation.reuseRateUpper reuse
  have demanded := no_reuse_supplied hooks before.machine id info generation value missing metadata
    notDead notType live representation.managed representation.current strict reuse head next bound allowed
  let middle := after (after before.machine (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
    (.boolean .addressReuse false)) (.index .slack 16) (.index .addressSlack value)
  obtain ⟨bytes,_,normalized⟩ := alignment
  obtain ⟨final,assigned,memory,borrow,threads,_race,payload⟩ := BumpAddress.no_reuse hooks middle id info generation
    ⟨value,bound⟩ missing metadata notDead notType live representation.managed representation.current
    representation.reuseRateLower representation.reuseRateUpper reuse
    (RawGenerator.normalized_exponent info.align bytes normalized) room positive
    (RawResources.frontier before generation representation)
  refine ⟨final,demanded.trans assigned,?_,memory,borrow,threads⟩
  have saved := congrArg (fun payload => payload.payload.user.choices) payload
  exact saved
/-- Full actual three-draw reused-hole call. The current raw pool supplies
physical safety and the actual source range supplies every selected row. -/
theorem reuse_pool_success (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : H) (id : AllocId) (info : AllocationInfo) (bucket : Array ReusableAddress)
    (cross : Bool) (value : Nat)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive id = true) (noRace : before.machine.dataRace = none)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (strict : (tapeAccess.get before.machine).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor]? = some (.boolean .addressReuse true))
    (next : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor+1]? = some (.boolean .addressCrossThread cross))
    (last : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor+2]? = some (.index .addressPool value))
    (bound : value < (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 -
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1) :
    ∃ base final, MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) before.machine = .ok base final ∧
      tapeAccess.get final = advance
        (advance (advance (tapeAccess.get before.machine)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
          (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
        (.index .pool ((ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 -
          (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1))
        (.index .addressPool value) ∧
      final.memory = before.machine.memory ∧ final.borrowTracker = before.machine.borrowTracker ∧ final.threads = before.machine.threads := by
  obtain ⟨bytes,abiBytes,normalized⟩ := alignment
  have reuseAllowed := ChoiceFloatSupport.allowed_of_supported .reuse _ true
    representation.reuseRateLower representation.reuseRateUpper reuse
  have crossAllowed := ChoiceFloatSupport.allowed_of_supported .crossThread _ cross
    representation.crossRateLower representation.crossRateUpper crossSupport
  have demanded := reuse_pool_supplied hooks before.machine id info generation bucket bytes cross value
    missing metadata notDead notType live representation.managed representation.current present abiBytes normalized
    strict reuse crossSupport head next last bound reuseAllowed crossAllowed
  let range := ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross
  let middle := after (after (after before.machine (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
    (.boolean .addressReuse true)) (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
    (.boolean .addressCrossThread cross)) (.index .pool (range.2-range.1)) (.index .addressPool value)
  have lower : range.1 ≤ range.1+value := by omega
  have upper : range.1+value < range.2 := by
    have ordered := (ReuseCandidate.range_spec bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1
    change value < range.2-range.1 at bound
    change range.1 ≤ range.2 at ordered
    omega
  obtain ⟨base,final,assigned,memory,borrow,threads,payload⟩ := RelocationAddress.reuse_assignment_at
    before generation representation hooks middle rfl rfl id info bucket cross (range.1+value)
    missing metadata notDead notType live noRace present ⟨bytes,abiBytes,normalized⟩ reuse crossSupport lower upper
  refine ⟨base,final,demanded.trans assigned,?_,memory,borrow,threads⟩
  exact congrArg (fun payload => payload.payload.user.choices) payload
/-- Full actual three-draw empty-hole call, including absent alignment buckets.
The pure ensured-bucket query classifies this branch; prepare success is derived
from the total source prefix proof and is not an input law. -/
theorem reuse_empty_success (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : H) (id : AllocId) (info : AllocationInfo) (bucket : Array ReusableAddress)
    (bytes : UInt64) (cross : Bool) (value : Nat)
    (missing : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : before.machine.memory.isAllocLive id = true)
    (present : ((reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2).pool[info.align.pow2]? = some bucket)
    (empty : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2 =
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1)
    (abiBytes : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (strict : (tapeAccess.get before.machine).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor]? = some (.boolean .addressReuse true))
    (next : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor+1]? = some (.boolean .addressCrossThread cross))
    (last : (tapeAccess.get before.machine).inputs[(tapeAccess.get before.machine).cursor+2]? = some (.index .addressSlack value))
    (bound : value < 16)
    (room : RawGenerator.Room generation.generator info.size info.align ⟨value,bound⟩)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ final, MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) before.machine =
      .ok (RawGenerator.base generation.generator info.align ⟨value,bound⟩) final ∧
      final.memory = before.machine.memory ∧ final.borrowTracker = before.machine.borrowTracker ∧
      final.threads = before.machine.threads ∧
      tapeAccess.get final = advance
        (advance (advance (tapeAccess.get before.machine)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
          (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
        (.index .slack 16) (.index .addressSlack value) := by
  have reuseAllowed := ChoiceFloatSupport.allowed_of_supported .reuse _ true
    representation.reuseRateLower representation.reuseRateUpper reuse
  have crossAllowed := ChoiceFloatSupport.allowed_of_supported .crossThread _ cross
    representation.crossRateLower representation.crossRateUpper crossSupport
  obtain ⟨actualBucket,loaded,prepared⟩ := ReuseEnsure.prepare generation.reusePool info.size info.align bytes
    (UInt32.ofNat before.machine.threads.activeThread.toNat) cross abiBytes normalized reuseAllowed crossAllowed
  have bucketEq : actualBucket = bucket := Option.some.inj (loaded.symm.trans present)
  subst actualBucket
  simp only [empty,beq_self_eq_true,↓reduceIte] at prepared
  let pool := (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2
  have demanded := reuse_empty_supplied_core hooks before.machine id info generation pool cross value
    missing metadata notDead notType live representation.managed representation.current strict
    reuse crossSupport head next last bound prepared
  let middle := after (staged
    (after (after before.machine (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
      (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
    before.machine.user.addresses generation pool) (.index .slack 16) (.index .addressSlack value)
  have rates := ReuseEnsure.rates generation.reusePool info.align.pow2
  obtain ⟨final,assigned,memory,borrow,threads,_race,payload⟩ := BumpAddress.empty_bucket hooks middle id info
    {generation with reusePool := pool} ⟨value,bound⟩ bucket bytes cross missing metadata notDead notType live
    representation.managed rfl present abiBytes normalized
    (by simpa only [pool,rates.1] using reuseAllowed)
    (by simpa only [pool,rates.2] using crossAllowed)
    empty room positive (RawResources.frontier before generation representation)
  refine ⟨final,demanded.trans assigned,memory,borrow,threads,?_⟩
  exact congrArg (fun payload => payload.payload.user.choices) payload
theorem reuse_empty_success_at (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : H) (state : S)
    (addressesSame : state.user.addresses = before.machine.user.addresses)
    (id : AllocId) (info : AllocationInfo) (bucket : Array ReusableAddress)
    (bytes : UInt64) (cross : Bool) (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId)
    (live : state.memory.isAllocLive id = true) (noRace : state.dataRace = none)
    (present : ((reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2).pool[info.align.pow2]? = some bucket)
    (empty : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).2 =
      (ReuseCandidate.candidate bucket info.size (UInt32.ofNat state.threads.activeThread.toNat) cross).1)
    (abiBytes : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (strict : (tapeAccess.get state).policy = .strict)
    (reuse : Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
    (crossSupport : Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (head : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor]? = some (.boolean .addressReuse true))
    (next : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+1]? = some (.boolean .addressCrossThread cross))
    (last : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor+2]? = some (.index .addressSlack value))
    (bound : value < 16)
    (room : RawGenerator.Room generation.generator info.size info.align ⟨value,bound⟩)
    (positive : 0 < generation.generator.nextBaseAddr.toNat) :
    ∃ final, MachineAddress.addrFromAllocId tapeAccess hooks id (some .other) state =
      .ok (RawGenerator.base generation.generator info.align ⟨value,bound⟩) final ∧
      final.memory = state.memory ∧ final.borrowTracker = state.borrowTracker ∧
      final.threads = state.threads ∧
      tapeAccess.get final = advance
        (advance (advance (tapeAccess.get state)
          (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
          (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
        (.index .slack 16) (.index .addressSlack value) ∧
      AddressChoicePlan.assignedState
        (({state.user.addresses with
          generation := some {generation with
            reusePool := (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2}} : GlobalAddressState).addrFromAllocId id
          (some ⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat state.threads.activeThread.toNat⟩)
          ⟨true,cross,0,⟨value,bound⟩⟩) = .ok final.user.addresses ∧ final.dataRace = state.dataRace ∧
      final.user.payload.payload.user.runtime = state.user.payload.payload.user.runtime ∧
      RelocationContext.view final.user.payload = RelocationContext.view state.user.payload := by
  have managed : state.user.addresses.addressMode = .managed := by simpa only [addressesSame] using representation.managed
  have current : state.user.addresses.generation = some generation := by simpa only [addressesSame] using representation.current
  have reuseAllowed := ChoiceFloatSupport.allowed_of_supported .reuse _ true
    representation.reuseRateLower representation.reuseRateUpper reuse
  have crossAllowed := ChoiceFloatSupport.allowed_of_supported .crossThread _ cross
    representation.crossRateLower representation.crossRateUpper crossSupport
  obtain ⟨actualBucket,loaded,prepared⟩ := ReuseEnsure.prepare generation.reusePool info.size info.align bytes
    (UInt32.ofNat state.threads.activeThread.toNat) cross abiBytes normalized reuseAllowed crossAllowed
  have bucketEq : actualBucket = bucket := Option.some.inj (loaded.symm.trans present)
  subst actualBucket
  simp only [empty,beq_self_eq_true,↓reduceIte] at prepared
  let pool := (reuse_actual ".ReusePool.ensureSubpool") generation.reusePool info.align.pow2
  have demanded := reuse_empty_supplied_core hooks state id info generation pool cross value
    missing metadata notDead notType live managed current strict
    reuse crossSupport head next last bound prepared
  let middle := after (staged
    (after (after state (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits) (.boolean .addressReuse true))
      (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits) (.boolean .addressCrossThread cross))
    state.user.addresses generation pool) (.index .slack 16) (.index .addressSlack value)
  have rates := ReuseEnsure.rates generation.reusePool info.align.pow2
  obtain ⟨final,assigned,memory,borrow,threads,_race,payload⟩ := BumpAddress.empty_bucket hooks middle id info
    {generation with reusePool := pool} ⟨value,bound⟩ bucket bytes cross missing metadata notDead notType live
    managed rfl present abiBytes normalized
    (by simpa only [pool,rates.1] using reuseAllowed)
    (by simpa only [pool,rates.2] using crossAllowed)
    empty room positive (by
      change ∀ row ∈ state.user.addresses.intToPtrMap, row.address.toNat < generation.generator.nextBaseAddr.toNat
      simpa only [addressesSame] using RawResources.frontier before generation representation)
  have successor := RelocationPost.assignment_state hooks middle id info ⟨true,cross,0,⟨value,bound⟩⟩
    missing metadata notDead notType live managed noRace _ final assigned
  refine ⟨final,demanded.trans assigned,memory,borrow,threads,?_,successor,_race,(congrArg (fun payload => payload.payload.user.runtime) payload),(by have projected := congrArg RelocationContext.view payload; exact projected)⟩
  · exact congrArg (fun payload => payload.payload.user.choices) payload
end EmptyFunction.RelocationChoices
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationChoices.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation choices axiom {dependency} in {name}"
