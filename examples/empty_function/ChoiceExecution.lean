import empty_function.ChoiceAdmission
import empty_function.RawStackAddress
import Miri.Input.EvalPointerSource

/-! Actual supplied stack-address demand, before deterministic assignment.
The assignment may still fail for a non-choice reason. Its outcome is retained,
and the supplied-tape condition does not rule it out. -/
namespace EmptyFunction.ChoiceExecution
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Input
open EmptyFunction.ChoiceSupply
set_option autoImplicit false

abbrev Payload := ValidityMachine.Control
  (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit Configuration.MinimalHost)
abbrev S := MachineAddress.State MiriMemoryKind Payload
abbrev H := MachineAddress.Hooks MiriMemoryKind Payload

def tapeAccess : ExecutionChoices.Access S := EvalPointerSource.tape

def afterDraw (state : S) (value : Nat) : S :=
  tapeAccess.put state (advance (tapeAccess.get state) (.index .slack 16) (.index .addressSlack value))

/-- Every supported slack input is covered. The real address algorithm consumes
it exactly once and then runs real source assign, whose error/success is kept. -/
theorem stack_supplied (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (value : Nat)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (currentGeneration : state.user.addresses.generation = some generation)
    (strict : (tapeAccess.get state).policy = .strict)
    (head : (tapeAccess.get state).inputs[(tapeAccess.get state).cursor]? =
      some (.index .addressSlack value))
    (supported : value < 16) :
    MachineAddress.addrFromAllocId tapeAccess hooks id (some .stack) state =
      MachineAddress.assign hooks id (some .stack) ⟨false,false,0,⟨value,supported⟩⟩ (afterDraw state value) := by
  simpa [afterDraw,advance,sourceRequest,IndexKind.site] using
    MachineAddress.stack_miss_supplied tapeAccess hooks state id info generation
      (tapeAccess.get state) value missing metadata data live managed currentGeneration
      rfl strict head supported

/-- The source tape lens reads precisely the cursor/event update emitted by
the supplied request, without mutating memory or the address tables. -/
theorem afterDraw_tape (state : S) (value : Nat) :
    tapeAccess.get (afterDraw state value) =
      advance (tapeAccess.get state) (.index .slack 16) (.index .addressSlack value) := rfl

/-- Deterministic managed assignment preserves the entire tape on errors as
well as success. This proves no second hidden request consumes the suffix. -/
theorem assign_tape (hooks : H) (state : S) (id : AllocId)
    (choices : AllocAddresses.AddressRandomChoices)
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none) :
    tapeAccess.get (MachineAddress.resultState (MachineAddress.assign hooks id (some .stack) choices state)) =
      tapeAccess.get state := by
  have saved := MachineAddress.assign_managed_payload hooks state id (some .stack) choices managed noRace
  exact congrArg (fun payload => payload.payload.user.choices) saved

/-- A stack grammar fit supplies an arbitrary legal value, not a fixed seed.
The actual operation has the exact request decomposition above for that value. -/
theorem stack_from_environment (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (currentGeneration : state.user.addresses.generation = some generation)
    (noRace : state.dataRace = none)
    (supply : ChoiceSupply.Environment stackMissPlan (tapeAccess.get state)) :
    ∃ value, ∃ supported : value < 16,
      MachineAddress.addrFromAllocId tapeAccess hooks id (some .stack) state =
        MachineAddress.assign hooks id (some .stack) ⟨false,false,0,⟨value,supported⟩⟩ (afterDraw state value) ∧
      tapeAccess.get (MachineAddress.resultState
        (MachineAddress.addrFromAllocId tapeAccess hooks id (some .stack) state)) =
        advance (tapeAccess.get state) (.index .slack 16) (.index .addressSlack value) := by
  obtain ⟨value,bound,head⟩ := (stack_fits _).mp supply.fits
  have step := stack_supplied hooks state id info generation value missing metadata data live
    managed currentGeneration supply.strict head bound
  refine ⟨value,bound,step,?_⟩
  rw [step,assign_tape hooks (afterDraw state value) id _ (by exact managed) (by exact noRace)]
  exact afterDraw_tape state value

theorem stack_attempt_head (initial : AllocAddresses.GlobalAddressState) (id : AllocId)
    (info : AllocAddresses.AllocationAddressInfo) (generation : AllocAddresses.AddressGenerationState) (tape : ExecutionChoices.Tape)
    (missing : initial.baseAddr.find? (fun row => row.allocId == id) = none)
    (data : info.kind = .liveData) (live : info.live = true)
    (stack : info.memoryKind = some .stack)
    (managed : initial.addressMode = .managed)
    (currentGeneration : initial.generation = some generation)
    (fits : Fits (AddressChoicePlan.attempt initial id info (fun _ => .done : AllocAddresses.GlobalAddressState → Plan 0)) tape) :
    ∃ value,value < 16 ∧ tape.inputs[tape.cursor]? = some (.index .addressSlack value) := by
  simp only [AddressChoicePlan.attempt,missing,Option.isSome_none,data,live,managed,stack,
    currentGeneration] at fits
  simp only [Bool.false_eq_true,Bool.not_true,↓reduceIte] at fits
  have kd : (AllocAddresses.AllocationAddressKind.liveData == AllocAddresses.AllocationAddressKind.dead) = false := by decide
  have kt : (AllocAddresses.AllocationAddressKind.liveData == AllocAddresses.AllocationAddressKind.typeId) = false := by decide
  have managedMode : (AllocAddresses.AddressSpaceMode.managed != AllocAddresses.AddressSpaceMode.managed) = false := by decide
  have stackKind : (AllocAddresses.AddressMemoryKind.stack == AllocAddresses.AddressMemoryKind.stack) = true := by decide
  simp only [kd,kt,managedMode,stackKind,Bool.false_or,Bool.false_eq_true,↓reduceIte] at fits
  simp only [fits_pad] at fits
  simp only [AddressChoicePlan.select,AllocAddresses.ReusePool.prepareTakeAddr,beq_self_eq_true,↓reduceIte,Id.run] at fits
  rcases fits with ⟨input,supported,head,_⟩
  cases supported with
  | index kind count value bound => exact ⟨value,bound,head⟩

/-- A source-derived projected plan either retains allocation failure or
supplies the actual arbitrary slack head. This does not assume reservation or
address assignment success, and does not hide failure in choice admission. -/
theorem projected_head {s : WholeCall.Static} {p : WholeCall.Packet}
    (binding : SourceChoicePlan.ProjectedBinding s p)
    (supply : SourceChoicePlan.ProjectedEnvironment binding)
    (generation : AllocAddresses.AddressGenerationState)
    (managed : p.before.machine.user.addresses.addressMode = .managed)
    (currentGeneration : p.before.machine.user.addresses.generation = some generation) :
    match p.before.machine.memory.reserveAllocId with
    | (_, .error _) => True
    | (_, .ok id) =>
      p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none →
      ∃ value, value < 16 ∧
        p.before.machine.user.payload.payload.user.choices.inputs[
          p.before.machine.user.payload.payload.user.choices.cursor]? =
            some (.index .addressSlack value) := by
  have fits := supply.fits
  cases reserved : p.before.machine.memory.reserveAllocId with
  | mk memory result =>
    cases result with
    | error error => simp
    | ok id =>
      simp only
      intro missing
      simp only [SourceChoicePlan.projectedPlan,reserved] at fits
      exact stack_attempt_head p.before.machine.user.addresses id
        { kind := .liveData, live := true,
          size := binding.destination.baseLayout.layout.size,
          align := binding.destination.baseLayout.layout.align.abi,
          memoryKind := some .stack,
          thread := UInt32.ofNat p.before.machine.threads.activeThread.toNat }
        generation p.before.machine.user.payload.payload.user.choices
        missing rfl rfl rfl managed currentGeneration fits

/-- The adopted choice-admission record selects the raw projected plan.
Allocation failure remains a separate non-choice branch; in the successful
reservation branch the next required response has the exact source site and
full Fin16 support. No address-operation success is an input assumption. -/
theorem caller_projected_head (s : WholeCall.Static) (p : WholeCall.Packet)
    (environment : ChoiceAdmission.Environment s p)
    (current : InputDraft.CurrentInputDraft s p)
    (needed : InputDraft.NeedsEnclosingAllocation p) :
    ∃ binding : SourceChoicePlan.ProjectedBinding s p,
      SourceChoicePlan.ProjectedEnvironment binding ∧
      (match p.before.machine.memory.reserveAllocId with
      | (_, .error _) => True
      | (_, .ok id) =>
        p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none →
        ∃ value, value < 16 ∧
          p.before.machine.user.payload.payload.user.choices.inputs[
            p.before.machine.user.payload.payload.user.choices.cursor]? =
              some (.index .addressSlack value)) := by
  obtain ⟨binding,supply⟩ := environment.projected needed
  refine ⟨binding,supply,?_⟩
  cases reserved : p.before.machine.memory.reserveAllocId with
  | mk after outcome =>
    cases outcome with
    | error error => trivial
    | ok id =>
      have active : InputDraft.AllocatorActive p.before := EmptyFunction.AllocatorActive.of_success _ _ _ reserved
      obtain ⟨generation,representation⟩ := current.projectedGeneration needed active
      have supplied := projected_head binding supply generation representation.managed representation.current
      simpa only [reserved] using supplied

open Lean Elab Tactic in
elab "unfold_machine_address_helpers" : tactic => do
  for suffix in [".MachineAddress.addresses", ".MachineAddress.finish", ".MachineAddress.setAddresses"] do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := found | throwError "expected one source helper {suffix}"
    evalTactic (← `(tactic| unfold $(mkIdent name)))

/-- Actual machine assignment, from current metadata and arithmetic/frontier
facts. The low-level success fact is proved internally from those raw inputs. -/
theorem assign_stack_ready (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (choices : AllocAddresses.AddressRandomChoices)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    ∃ after, MachineAddress.assign hooks id (some .stack) choices state =
      .ok (RawGenerator.base generation.generator info.align choices.slack) after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.dataRace = state.dataRace ∧
      after.user.payload = state.user.payload := by
  let addressInfo : AllocAddresses.AllocationAddressInfo := {
    kind := .liveData, live := true, size := info.size, align := info.align,
    memoryKind := some .stack, thread := UInt32.ofNat state.threads.activeThread.toNat }
  have ready := RawStackAddress.assigned state.user.addresses generation id addressInfo choices
    managed current missing rfl rfl rfl alignment room positive frontier
  cases actual : state.user.addresses.addrFromAllocId id (some addressInfo) choices ⟨none⟩ with
  | mk afterAddress outcome =>
    have outcomeReady : outcome = .ok (.ready (RawGenerator.base generation.generator info.align choices.slack)) := by
      simpa only [actual] using ready
    subst outcome
    simp only [addressInfo] at actual
    unfold MachineAddress.assign
    unfold_machine_address_helpers
    simp [missing,metadata,data,live,managed,actual,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]

/-- Supplied legal choices plus raw current geometry eliminate all stack-address
errors; the real tape advances once with the selected response recorded. -/
theorem stack_success_from_environment (hooks : H) (state : S) (id : AllocId)
    (info : AllocationInfo) (generation : AllocAddresses.AddressGenerationState)
    (missing : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed)
    (current : state.user.addresses.generation = some generation)
    (noRace : state.dataRace = none)
    (alignment : info.align.pow2 ≤ 29)
    (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat)
    (supply : ChoiceSupply.Environment stackMissPlan (tapeAccess.get state)) :
    ∃ (value : Nat) (supported : value < 16) (after : S),
      MachineAddress.addrFromAllocId tapeAccess hooks id (some .stack) state =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩) after ∧
      tapeAccess.get after = advance (tapeAccess.get state)
        (.index .slack 16) (.index .addressSlack value) := by
  obtain ⟨value,bound,step,tape⟩ := stack_from_environment hooks state id info generation
    missing metadata data live managed current noRace supply
  obtain ⟨after,ready,_saved⟩ := assign_stack_ready hooks (afterDraw state value) id info generation
    ⟨false,false,0,⟨value,bound⟩⟩ missing metadata data live managed current
    alignment (room _) positive frontier
  refine ⟨value,bound,after,step.trans ready,?_⟩
  simpa only [step,ready,MachineAddress.resultState] using tape

end EmptyFunction.ChoiceExecution

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.ChoiceExecution." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty_function choice-execution axiom {dependency}"
