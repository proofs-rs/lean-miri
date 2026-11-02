import empty_function.RawResources
import Miri.Interpreter.ExecutionAddressChoices
import Miri.Input.EvalCoreMachine
namespace EmptyFunction.ChoiceProjection
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
abbrev S := PointerMachine.State MiriMemoryKind ChoiceExecution.Payload
abbrev H := PointerMachine.Hooks MiriMemoryKind ChoiceExecution.Payload

def tapeAccess : ExecutionChoices.Access S := EvalCoreMachine.tape

def afterDraw (state : S) (value : Nat) : S :=
  tapeAccess.put state (advance (tapeAccess.get state) (.index .slack 16) (.index .addressSlack value))

open Lean Elab Tactic in
elab "unfold_projection_address_helpers" : tactic => do
  for suffix in [".ExecutionAddressChoices.setAddresses", ".ExecutionAddressChoices.slack"] do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := found | throwError "expected one source helper {suffix}"
    evalTactic (← `(tactic| unfold $(mkIdent name)))

theorem stack_request (hooks : H) (state : S) (id : AllocId) (info : AllocationInfo)
    (generation : AllocAddresses.AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation) :
    ExecutionAddressChoices.addrFromAllocId tapeAccess hooks id (some .stack) state =
      (do let selected ← ExecutionChoices.index tapeAccess .addressSlack 16
          if valid : selected < 16 then
            PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,⟨selected,valid⟩⟩
          else throw (StepError.invalidProgram "checked address slack exceeded support")) state := by
  unfold ExecutionAddressChoices.addrFromAllocId
  unfold_projection_address_helpers
  simp [missing,metadata,data,live,managed,current,AllocAddresses.ReusePool.prepareTakeAddr,Id.run,
    get,getThe,MonadStateOf.get,EStateM.get,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,bind,EStateM.bind,pure,EStateM.pure]
  simp only [←current,←managed]
  cases supplied : ExecutionChoices.index tapeAccess .addressSlack 16 state with
  | error error after => simp
  | ok value after =>
    by_cases within : value < 16
    · simp [within,EStateM.pure]
    · simp [within,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

open Lean Elab Tactic in
elab "unfold_pointer_address_helpers" : tactic => do
  for suffix in [".PointerMachine.addresses", ".PointerMachine.finish", ".PointerMachine.setAddresses"] do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := found | throwError "expected one source helper {suffix}"
    evalTactic (← `(tactic| unfold $(mkIdent name)))

/-- Actual machine assignment, from current metadata and arithmetic/frontier
facts. The low-level success fact is proved internally from those raw inputs. -/
theorem assign_stack_ready (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (choices : AllocAddresses.AddressRandomChoices)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    ∃ after, PointerMachine.addrFromAllocId hooks id (some .stack) choices state =
      .ok (RawGenerator.base generation.generator info.align choices.slack) after ∧
      after.machine.memory = state.machine.memory ∧ after.machine.borrowTracker = state.machine.borrowTracker ∧
      after.machine.threads = state.machine.threads ∧ after.machine.dataRace = state.machine.dataRace ∧
      after.machine.user.payload = state.machine.user.payload ∧ after.stack = state.stack := by
  let addressInfo : AllocAddresses.AllocationAddressInfo := {
    kind := .liveData, live := true, size := info.size, align := info.align,
    memoryKind := some .stack, thread := UInt32.ofNat state.machine.threads.activeThread.toNat }
  have ready := RawStackAddress.assigned state.machine.user.addresses generation id addressInfo choices
    managed current missing rfl rfl rfl alignment room positive frontier
  cases actual : state.machine.user.addresses.addrFromAllocId id (some addressInfo) choices ⟨none⟩ with
  | mk afterAddress outcome =>
    have outcomeReady : outcome = .ok (.ready (RawGenerator.base generation.generator info.align choices.slack)) := by
      simpa only [actual] using ready
    subst outcome
    simp only [addressInfo] at actual
    unfold PointerMachine.addrFromAllocId
    unfold_pointer_address_helpers
    simp [missing,metadata,data,live,managed,actual,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]


/-- The address operation actually used by canonical projected stack allocation.
Every supplied legal slack succeeds and preserves caller stack, memory, tracker
and all threads while recording exactly the one source choice event. -/
theorem stack_success (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29)
    (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat)
    (supply : ChoiceSupply.Environment stackMissPlan (tapeAccess.get state)) :
    ∃ (value : Nat) (supported : value < 16) (after : S),
      ExecutionAddressChoices.addrFromAllocId tapeAccess hooks id (some .stack) state =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩) after ∧
      tapeAccess.get after = advance (tapeAccess.get state)
        (.index .slack 16) (.index .addressSlack value) ∧
      after.machine.memory = state.machine.memory ∧
      after.machine.borrowTracker = state.machine.borrowTracker ∧
      after.machine.threads = state.machine.threads ∧ after.stack = state.stack := by
  obtain ⟨value,bound,head⟩ := (stack_fits _).mp supply.fits
  have requested := stack_request hooks state id info generation missing metadata data live managed current
  have draw := ExecutionChoices.index_supplied tapeAccess state (tapeAccess.get state)
    .addressSlack 16 value rfl supply.strict head bound
  have supplied : ExecutionAddressChoices.addrFromAllocId tapeAccess hooks id (some .stack) state =
      PointerMachine.addrFromAllocId hooks id (some .stack) ⟨false,false,0,⟨value,bound⟩⟩
        (afterDraw state value) := by
    rw [requested]
    simp only [bind,EStateM.bind,draw,bound,↓reduceDIte]
    rfl
  obtain ⟨after,ready,memory,borrow,threads,_race,payload,stack⟩ :=
    assign_stack_ready hooks (afterDraw state value) id info generation
      ⟨false,false,0,⟨value,bound⟩⟩ missing metadata data live managed current
      alignment (room _) positive frontier
  refine ⟨value,bound,after,supplied.trans ready,?_,memory,borrow,threads,stack⟩
  change after.machine.user.payload.payload.user.choices = _
  rw [payload]
  rfl

open WholeCall in
/-- Concrete current resources discharge the canonical stack address call.
The parent allocation's preceding storage/tag/live prefix is still a separate
preservation obligation; it is not assumed successful by this theorem. -/
theorem current_resources (s : Static) (p : Packet)
    (resources : Specification.ResourceMargins s p)
    (generation : AllocAddresses.AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation p.before generation)
    (hooks : H) (id : AllocId) (info : AllocationInfo)
    (missing : p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : p.before.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : p.before.machine.memory.isAllocLive id = true)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (sizeBound : info.size.bytes.toNat ≤ resources.maximumSize)
    (alignBound : 2^info.align.pow2 ≤ resources.maximumAlignment)
    (supply : ChoiceSupply.Environment stackMissPlan (tapeAccess.get p.before)) :
    ∃ (value : Nat) (supported : value < 16) (after : S),
      ExecutionAddressChoices.addrFromAllocId tapeAccess hooks id (some .stack) p.before =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩) after ∧
      tapeAccess.get after = advance (tapeAccess.get p.before)
        (.index .slack 16) (.index .addressSlack value) ∧
      after.machine.memory = p.before.machine.memory ∧
      after.machine.borrowTracker = p.before.machine.borrowTracker ∧
      after.machine.threads = p.before.machine.threads ∧ after.stack = p.before.stack := by
  have minimum : 64 ≤ Specification.work s p := by unfold Specification.work; omega
  have one : 1 ≤ resources.budget := by have := resources.reserve; omega
  have allRoom := RawResources.room s p resources generation representation.current
    info.size info.align alignment sizeBound alignBound one
  obtain ⟨bytes,_,normalized⟩ := alignment
  exact stack_success hooks p.before id info generation missing metadata data live
    representation.managed representation.current
    (RawGenerator.normalized_exponent info.align bytes normalized) allRoom
    (resources.addresses generation representation.current).positiveCursor
    (RawResources.frontier p.before generation representation) supply

end EmptyFunction.ChoiceProjection
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ChoiceProjection." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved projection axiom {dependency} in {name}"
