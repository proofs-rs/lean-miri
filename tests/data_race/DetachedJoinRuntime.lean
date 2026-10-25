import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.UnixThreadMachine
import Miri.Interpreter.ExecutionChoiceBindings

/-! Runtime regression for `ThreadMachine.joinExclusive`, the connected
`thread.rs::join_thread_exclusive` path. The pinned source first rejects
Joined, self, and existing waiter cases, then delegates to `join_thread`,
whose Detached check must precede the status mutation, `after_join` sync, and
return-place write. These tests execute the runtime action against real
ThreadManager/ThreadStacks machine state rather than the abstract Join model.
-/

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
open Miri.Interpreter
open Miri.Interpreter.ThreadStacks
open Miri.Interpreter.ThreadMachine

structure Probe where
  runtime : Runtime Unit := {}
  events : Array String := #[]
  choices : ExecutionChoices.Tape := { inputs := #[] }
  reuseCalls : Nat := 0

abbrev TestState := ThreadStacks.State Nat Probe
abbrev TestM := ThreadStacks.M Nat Probe

private def fail {A : Type} : EStateM StepError TestState A :=
  throw (.unsupported "unused hook in DetachedJoinRuntime fixture")

private def testLayout : LocalLayout := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩

private def testDestination : MPlaceTy Provenance :=
  ⟨⟨Pointer.withoutProvenance 0, .none, none⟩, testLayout⟩

private def testCallHooks : CallHooks Provenance TestState Unit MachineHooks.FrameExtra
    Unit Unit Nat Nat := {
  debugAssertions := false
  getFrame := fail
  setFrame := fun _ => fail
  frameIndex := fail
  evalOperand := fun _ _ => fail
  evalPlace := fun _ _ _ => fail
  placeToOp := fun _ _ => fail
  forceAllocation := fun _ _ => fail
  functionSignature := fun _ _ => fail
  functionKind := fun _ => fail
  readPointer := fun _ _ => fail
  getPtrFn := fun _ _ => fail
  resolve := fun _ _ _ => fail
  fnAbiOfFnPtr := fun _ _ _ => fail
  fnAbiOfInstance := fun _ _ _ => fail
  requiresCallerLocation := fun _ => fail
  callerLocation := fail
  abiCanUnwind := fun _ => false
  abiVariadic := fun _ => false
  abiFixedCount := fun _ => 0
  abiArgs := fun _ => #[]
  abiReturn := fun _ => 0
  sameConvention := fun _ _ => false
  isRustCall := fun _ => false
  rustAbi := ()
  argLayout := fun _ => testLayout
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ => fail
  checkTargetFeatures := fun _ _ => fail
  tupleFields := fun _ => fail
  projectFnArg := fun _ _ _ => fail
  localLayout := fun _ _ => fail
  localSpan := fun _ _ => fail
  storageLiveDyn := fun _ _ _ => fail
  copyAllowTransmute := fun _ _ _ => fail
  protectArgument := fun _ _ => fail
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ _ _ => fail
  allocateStack := fun _ _ => fail
  copyToMemory := fun _ _ _ => fail
  vaListPtr := fun _ _ => fail
  writeZeroBytes := fun _ _ _ => fail
  vaListKeyField := fun _ _ => fail
  writePointerToMemory := fun _ _ _ => fail
  pushRaw := fun _ _ _ _ _ => fail
  pushDone := fun _ => fail
  popRaw := fun _ => fail
  cleanup := fun _ _ _ => fail
  afterFrameInit := fun _ => fail
  callExtra := fun _ _ _ _ _ _ _ => fail
  callIntrinsic := fun _ _ _ _ _ _ => fail
  callLlvmIntrinsic := fun _ _ _ _ _ => fail
  findMirOrEvalFn := fun _ _ _ _ _ _ _ => fail
  resolveVirtual := fun _ _ _ _ _ _ => fail
  isDynamic := fun _ => fail
  unpackDynForDrop := fun _ _ => fail
  resolveDropGlue := fun _ _ => fail
  mplaceToMutRef := fun _ _ => fail
  fakeUnitReturn := fun _ => fail
}

private def testFunctions : FunctionCalls.Hooks Provenance TestState Unit
    MachineHooks.FrameExtra Unit Unit Nat Nat := {
  call := testCallHooks
  loadMir := fun _ _ => fail
  unitLayout := testLayout
  fnAbiOfSignature := fun _ _ => fail
  callerLocationType := fail
  activeStackEmpty := fail
  originIsDummy := fail
  setOrigin := fun _ => fail
}

private def testAllocation : PlaceMachine.AllocationConfig Nat (ThreadStacks.Storage Probe) := {
  maximumObjectSize := Size.ofBytes 1024
  zeroedStorage := fun _ _ => none
  diagnostic := fun _ _ _ => throw (.unsupported "unused allocation diagnostic")
  allocationTail := fun _ _ _ => throw (.unsupported "unused allocation tail")
  adjustRootAddress := fun _ _ => throw (.unsupported "unused root adjustment")
}

private def recordEffect (effect : String) : TestM Unit :=
  modify fun state => { state with machine := { state.machine with user := {
    state.machine.user with user := { state.machine.user.user with
      events := state.machine.user.user.events.push effect } } } }

private def testHooks : ThreadMachine.Hooks Nat Probe Unit Unit Unit Nat Nat Unit := {
  runtime := Probe.runtime
  putRuntime := fun user runtime => { user with runtime }
  functions := testFunctions
  allocation := testAllocation
  machineMemoryKind := 0
  writeScalar := fun _ _ _ => recordEffect "destination-write"
  spans := ⟨⟨0⟩, false⟩
}

private def reuseAccess : ExecutionChoices.Access TestState := {
  get := fun state => state.machine.user.user.choices
  put := fun state tape => { state with machine := { state.machine with user :=
    { state.machine.user with user := { state.machine.user.user with choices := tape } } } }
}

private def reuseHooks : ThreadMachine.Hooks Nat Probe Unit Unit Unit Nat Nat Unit := {
  testHooks with
  chooseReuseClock := fun candidates => do
    modify fun state => { state with machine := { state.machine with user :=
      { state.machine.user with user := { state.machine.user.user with
        reuseCalls := state.machine.user.user.reuseCalls + 1 } } } }
    let rank ← ExecutionChoices.index reuseAccess .threadClockReuse candidates.length
    match candidates[rank]? with
    | some index => pure (some index)
    | none => throw (.invalidProgram "fixture choice escaped candidate support")
}

/-! Source117 integration regression: go through UnixThread.create and the
standard UnixThreadMachine.bind.start adapter. Only later callable-MIR lookup
is intentionally unsupported; the assertion observes the real chooser input,
the shared tape, and the resulting data-race clock state before that boundary. -/
private def pointerAbi : ABI.Scalar :=
  .Initialized (value := .Pointer AddressSpace.ZERO)
    (validRange := ⟨BitVec.ofNat 128 0, BitVec.ofNat 128 (2^64-1)⟩)

private def pointerLayout : LocalLayout := ⟨1, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Scalar pointerAbi,
  largestNiche := none, uninhabited := false, align := .new Align.EIGHT,
  size := Size.ofBytes 8, maxReprAlign := none, unadjustedAbiAlign := Align.EIGHT,
  reprC := false, randomizationSeed := 0 }⟩

private def connectedAccess : PlaceMachine.AccessConfig Nat (ThreadStacks.Storage Probe) := {
  runtime := RuntimeTargetDataLayout.default
  ghostMode := false
  globalKind := none
  globalHooks := {
    synchronizeMemory := fun _ state => state
    evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unused"⟩
    beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .ok ()⟩
    adjustGlobalAllocation := fun memory state _ _ => ⟨memory, state, .error "unused"⟩ }
  dynamicLayout := fun memory state _ => ⟨memory, state, .ok none⟩
  resolvePointer := fun _ pointer _ machine => .ok (.error pointer.offset.bytes) machine
  beforeAllocationAccess := fun _ => pure ()
  diagnostic := fun _ _ _ => pure ()
  weakMemoryWrite := fun _ _ => pure ()
  syncAccess := fun _ _ _ => pure ()
  retainTouched := fun machine _ => machine
  memoryError := fun error => .invalidProgram (reprStr error) }

private def unixBase : UnixThread.Hooks TestState := {
  pthreadLayout := pure pointerLayout
  unitPointerLayout := pure pointerLayout
  readScalar := fun _ => fail
  readPointer := fun _ => fail
  readImmediate := fun _ => fail
  dereference := fun _ _ => fail
  isNull := fun pointer => pure (pointer.offset.bytes == 0)
  scalarPointer := fun _ => fail
  scalarUsize := fun _ => fail
  readCString := fun _ => fail
  writeCString := fun _ _ _ => fail
  threads := return (← get).machine.threads
  putThreads := ThreadStacks.installManager
  start := fun _ _ _ _ => fail
  join := fun _ _ _ => fail
  detach := fun _ => fail
  hostUsizeBits := 64 }

private def setRecord (manager : ThreadManager) (id : ThreadId)
    (update : ThreadRecord → ThreadRecord) : ThreadManager :=
  { manager with threads := manager.threads.mapIdx fun index thread =>
      if index == id.toNat then update thread else thread }

private def makeManager (waiterCase : Bool) : Except ThreadError (ThreadManager × ThreadId × Option ThreadId) := do
  let manager := ThreadManager.initial false
  let (manager, target) ← ThreadManager.createThread manager 10
  let manager ← (ThreadManager.detachThread manager target false)
  let manager := setRecord manager target fun thread => { thread with state := .Terminated }
  if waiterCase then
    let (manager, waiter) ← ThreadManager.createThread manager 11
    let manager := setRecord manager waiter fun thread =>
      { thread with state := .Blocked (.Join target) none 91 }
    return (manager, target, some waiter)
  return (manager, target, none)

private def makeState (manager : ThreadManager) : Except StepError TestState := do
  let mut inactive : Array ThreadStacks.SavedStack := #[]
  for index in [:manager.threads.length] do
    let id ← match ThreadId.ofNat index with
      | .ok id => pure id
      | .error error => throw (.invalidProgram s!"test thread id: {repr error}")
    if id != manager.activeThread then
      inactive := inactive.push ⟨id, Stack.empty⟩
  let machine : MachineHooks.State Nat Probe := {
    stack := Stack.empty
    machine := {
      memory := MemoryState.empty
      borrowTracker := none
      dataRace := none
      threads := manager
      raceAllocations := #[]
      allocationSpans := #[]
      user := {} } }
  match ThreadStacks.attach machine inactive ⟨0⟩ with
  | .ok state => pure state
  | .error error => throw error

private def makeReuseState (manager : ThreadManager) (global : Option GlobalState)
    (probe : Probe := {}) : Except StepError TestState := do
  let mut inactive : Array ThreadStacks.SavedStack := #[]
  for index in [:manager.threads.length] do
    let id ← match ThreadId.ofNat index with
      | .ok id => pure id
      | .error error => throw (.invalidProgram s!"reuse test thread id: {repr error}")
    if id != manager.activeThread then inactive := inactive.push ⟨id, Stack.empty⟩
  let machine : MachineHooks.State Nat Probe := {
    stack := Stack.empty
    machine := {
      memory := MemoryState.empty
      borrowTracker := none
      dataRace := global
      threads := manager
      raceAllocations := #[]
      allocationSpans := #[]
      user := probe } }
  match ThreadStacks.attach machine inactive ⟨0⟩ with
  | .ok state => pure state
  | .error error => throw error

private def twoCandidateGlobal : GlobalState := Id.run do
  let ix0 := VectorIdx.ofU32 0 (by decide)
  let ix1 := VectorIdx.ofU32 1 (by decide)
  let ix2 := VectorIdx.ofU32 2 (by decide)
  let t1 := ThreadId.ofU32 1 (by decide)
  let t2 := ThreadId.ofU32 2 (by decide)
  let base := GlobalState.initial false false
  return { base with
    vectorClocks := [ThreadClockSet.default, ThreadClockSet.default, ThreadClockSet.default]
    vectorInfo := [ThreadId.MAIN_THREAD, t1, t2]
    threadInfo := [⟨some ix0, none⟩, ⟨some ix1, none⟩, ⟨some ix2, none⟩]
    reuseCandidates := [ix1, ix2] }

private def twoCandidateManager : Except ThreadError ThreadManager := do
  let (manager, _) ← ThreadManager.createThread (ThreadManager.initial false) 10
  let (manager, _) ← ThreadManager.createThread manager 11
  pure manager

private def runSpawn (label : String) (hooks : ThreadMachine.Hooks Nat Probe Unit Unit Unit Nat Nat Unit)
    (manager : ThreadManager) (global : Option GlobalState) (reuse : Option VectorIdx)
    (probe : Probe := {}) : IO TestState := do
  let initial ← match makeReuseState manager global probe with
    | .ok state => pure state
    | .error error => throw (IO.userError s!"{label}: setup: {reprStr error}")
  let (after, outcome) := MachineHooks.run
    (ThreadMachine.startRegularThread hooks () none (Pointer.withoutProvenance 101)
      () ⟨.uninit, testLayout⟩ testLayout reuse)
    initial
  match outcome with
  | .error (.callback _) | .error (.unsupported _) => pure after
  | .error error => throw (IO.userError s!"{label}: unexpected stop: {reprStr error}")
  | .ok _ => throw (IO.userError s!"{label}: expected fixture stop after thread creation")

private def pointerOperand (address : UInt64) : IO (OpTy Provenance) := do
  let pointer : Pointer (Option Provenance) := Pointer.withoutProvenance address
  let scalar ← match Scalar.fromMaybePointer RuntimeTargetDataLayout.default.base pointer with
    | .ok scalar => pure scalar
    | .error error => throw (IO.userError s!"pointer operand setup: {reprStr error}")
  pure ⟨.immediate (.scalar scalar), pointerLayout⟩

private def runUnixCreate (manager : ThreadManager) (global : GlobalState)
    (tape : ExecutionChoices.Tape) (reuse : Option VectorIdx := none) : IO TestState := do
  let hooks := ExecutionChoiceBindings.threadClockReuse reuseAccess
    testHooks
  let unix := UnixThreadMachine.bind hooks connectedAccess () () reuse
    (fun _ _ => pure none) unixBase
  let initial ← match makeReuseState manager (some global) {choices := tape} with
    | .ok state => pure state
    | .error error => throw (IO.userError s!"Unix create setup: {reprStr error}")
  let op ← pointerOperand 0x1000
  let (after, _) := MachineHooks.run (UnixThread.create unix op op op op) initial
  return after

private def managerSnapshot (manager : ThreadManager) : String := reprStr manager

private def runtimeSnapshot (runtime : Runtime Unit) : String :=
  s!"{runtime.nextCallback}:{runtime.tlsCallbacks.size}:{runtime.joins.size}:{runtime.affinity.map Array.size}"

private def runRejected (label : String) (manager : ThreadManager) (joined : ThreadId)
    (expected : StepError) : IO String := do
  let initial ← match makeState manager with
    | .ok state => pure state
    | .error error => throw (IO.userError s!"{label}: state: {reprStr error}")
  let beforeManager := managerSnapshot initial.machine.threads
  let beforeRuntime := runtimeSnapshot initial.machine.user.user.runtime
  let beforeEvents := initial.machine.user.user.events
  let (after, outcome) := MachineHooks.run
    (ThreadMachine.joinExclusive testHooks () joined (Scalar.fromBool true) testDestination)
    initial
  match outcome with
    | .error error =>
      unless reprStr error == reprStr expected do
        throw (IO.userError s!"{label}: wrong rejection: {reprStr error}")
    | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted detached join")
  unless managerSnapshot after.machine.threads == beforeManager do
    throw (IO.userError s!"{label}: thread manager mutated on rejection")
  unless runtimeSnapshot after.machine.user.user.runtime == beforeRuntime do
    throw (IO.userError s!"{label}: callback runtime mutated on rejection")
  unless after.machine.user.user.events == beforeEvents && beforeEvents.isEmpty do
    throw (IO.userError s!"{label}: sync or destination write ran: {reprStr after.machine.user.user.events}")
  return s!"{label}:rejected-before-effects"

def main : IO Unit := do
  let (joinable, target) ← match ThreadManager.createThread (ThreadManager.initial false) 10 with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"joined setup: {reprStr error}")
  let joined := setRecord joinable target fun thread =>
    { thread with joinStatus := .Joined, state := .Terminated }
  let joinedLine ← runRejected "joined" joined target
    (.undefinedBehavior "trying to join an already joined thread")

  let self := setRecord (ThreadManager.initial false) ThreadId.MAIN_THREAD fun thread =>
    { thread with joinStatus := .Detached }
  let selfLine ← runRejected "self" self ThreadId.MAIN_THREAD
    (.undefinedBehavior "trying to join itself")

  let (waiterManager, waiterTarget, _) ← match makeManager true with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"waiter setup: {reprStr error}")
  let waiterLine ← runRejected "waiter" waiterManager waiterTarget
    (.invalidProgram "exclusive join already has waiters")

  let (detached, detachedTarget, _) ← match makeManager false with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"detached setup: {reprStr error}")
  let detachedLine ← runRejected "detached" detached detachedTarget
    (.undefinedBehavior "trying to join a detached thread")
  for line in [joinedLine, selfLine, waiterLine, detachedLine] do
    IO.println line

  let ix0 := VectorIdx.ofU32 0 (by decide)
  let ix1 := VectorIdx.ofU32 1 (by decide)
  let ix2 := VectorIdx.ofU32 2 (by decide)
  let emptyGlobal := GlobalState.initial false false
  let emptyRun ← runSpawn "no-candidates" reuseHooks (ThreadManager.initial false)
    (some emptyGlobal) none
  unless emptyRun.machine.user.user.reuseCalls == 0 &&
      emptyRun.machine.user.user.choices.cursor == 0 do
    throw (IO.userError "empty source candidate set drew a reuse choice")
  unless (emptyRun.machine.dataRace.map fun global => global.vectorClocks.length) == some 2 do
    throw (IO.userError "empty candidate spawn did not complete data-race thread-created")
  IO.println "reuse:no-candidates:no-draw:created"

  let manager ← match twoCandidateManager with
    | .ok manager => pure manager
    | .error error => throw (IO.userError s!"two-candidate manager: {repr error}")
  let candidates := GlobalState.reusableCandidates twoCandidateGlobal
  unless candidates == [ix1, ix2] do
    throw (IO.userError s!"expected two safe source candidates, got {repr candidates}")
  let tape : ExecutionChoices.Tape := { inputs := #[.index .threadClockReuse 1] }
  let selectedRun ← runSpawn "candidate-index-one" reuseHooks manager
    (some twoCandidateGlobal) none { choices := tape }
  unless selectedRun.machine.user.user.reuseCalls == 1 &&
      selectedRun.machine.user.user.choices.cursor == 1 &&
      selectedRun.machine.user.user.choices.events.size == 1 do
    throw (IO.userError "safe candidate choice was not consumed exactly once")
  let some selectedGlobal := selectedRun.machine.dataRace |
    throw (IO.userError "candidate spawn lost global clock state")
  let child := ThreadId.ofU32 3 (by decide)
  unless selectedGlobal.vectorInfo[2]? == some child &&
      selectedGlobal.reuseCandidates == [ix1] do
    throw (IO.userError "choice index 1 did not reuse the second safe source clock")
  IO.println "reuse:two-safe-candidates:index-1:reused-second"

  let badTape : ExecutionChoices.Tape := { inputs := #[.index .threadClockReuse 2] }
  let badIndexRun ← runSpawn "out-of-support-index" reuseHooks manager
    (some twoCandidateGlobal) none { choices := badTape }
  unless badIndexRun.machine.user.user.reuseCalls == 1 &&
      badIndexRun.machine.user.user.choices.cursor == 0 &&
      badIndexRun.machine.user.user.choices.events.isEmpty do
    throw (IO.userError "out-of-support reuse index was consumed or bypassed")
  IO.println "reuse:bad-index:rejected-before-consumption"

  let explicitRun ← runSpawn "explicit-existing-index" reuseHooks manager
    (some twoCandidateGlobal) (some ix2)
  unless explicitRun.machine.user.user.reuseCalls == 0 &&
      explicitRun.machine.user.user.choices.cursor == 0 do
    throw (IO.userError "explicit reuse index unexpectedly drew a choice")
  let some explicitGlobal := explicitRun.machine.dataRace |
    throw (IO.userError "explicit reuse spawn lost global clock state")
  unless explicitGlobal.vectorInfo[2]? == some child &&
      explicitGlobal.reuseCandidates == [ix1] do
    throw (IO.userError "explicit safe reuse index did not preserve existing behavior")
  IO.println "reuse:explicit-index:preserved:no-draw"

  let invalidExplicitRun ← runSpawn "explicit-unsafe-index" reuseHooks manager
    (some twoCandidateGlobal) (some ix0)
  unless invalidExplicitRun.machine.user.user.reuseCalls == 0 &&
      invalidExplicitRun.machine.user.user.choices.cursor == 0 do
    throw (IO.userError "invalid explicit reuse index fell back to a random choice")
  let some unchangedGlobal := invalidExplicitRun.machine.dataRace |
    throw (IO.userError "invalid explicit reuse index lost global clock state")
  unless unchangedGlobal.vectorInfo == twoCandidateGlobal.vectorInfo &&
      unchangedGlobal.reuseCandidates == twoCandidateGlobal.reuseCandidates do
    throw (IO.userError "invalid explicit reuse index changed source clocks")
  IO.println "reuse:unsafe-explicit-index:rejected:no-fallback"

  let noRaceRun ← runSpawn "no-data-race-state" reuseHooks (ThreadManager.initial false)
    none none
  unless noRaceRun.machine.user.user.reuseCalls == 0 &&
      noRaceRun.machine.user.user.choices.cursor == 0 && noRaceRun.machine.dataRace.isNone do
    throw (IO.userError "spawn without data-race state attempted a reuse choice")
  IO.println "reuse:no-data-race-state:no-draw"

  let connectedTape : ExecutionChoices.Tape :=
    { inputs := #[.index .threadClockReuse 1] }
  let connectedRun ← runUnixCreate manager twoCandidateGlobal connectedTape
  let expectedConnectedEvent : ExecutionChoices.Event := {
    request := .index .threadClockReuse 2
    input := .index .threadClockReuse 1 }
  unless connectedRun.machine.user.user.choices.cursor == 1 &&
      reprStr connectedRun.machine.user.user.choices.events ==
        reprStr (#[expectedConnectedEvent] : Array ExecutionChoices.Event) do
    throw (IO.userError "UnixThread.create did not draw from the two safe thread-clock candidates")
  let some connectedGlobal := connectedRun.machine.dataRace |
    throw (IO.userError "UnixThread.create lost data-race state")
  unless connectedGlobal.vectorInfo[2]? == some child &&
      connectedGlobal.reuseCandidates == [ix1] do
    throw (IO.userError "UnixThread.create did not pass the selected clock through threadCreated")
  IO.println "reuse:unix-thread-create:bound-choice:two-safe-candidates:index-1"

  let connectedEmptyGlobal := { twoCandidateGlobal with reuseCandidates := [] }
  let connectedEmpty ← runUnixCreate manager connectedEmptyGlobal {inputs := #[]}
  unless connectedEmpty.machine.user.user.choices.cursor == 0 &&
      connectedEmpty.machine.user.user.choices.events.isEmpty &&
      (connectedEmpty.machine.dataRace.map fun global => global.vectorClocks.length) == some 4 do
    throw (IO.userError "UnixThread.create sampled empty support or failed to create a fresh clock")
  IO.println "reuse:unix-thread-create:empty-support:no-draw"

  let connectedBad ← runUnixCreate manager twoCandidateGlobal
    {inputs := #[.index .threadClockReuse 2]}
  unless connectedBad.machine.user.user.choices.cursor == 0 &&
      connectedBad.machine.user.user.choices.events.isEmpty &&
      (connectedBad.machine.dataRace.map fun global =>
        (global.vectorInfo, global.reuseCandidates)) ==
        some (twoCandidateGlobal.vectorInfo, twoCandidateGlobal.reuseCandidates) do
    throw (IO.userError "UnixThread.create accepted an out-of-support clock index")
  IO.println "reuse:unix-thread-create:bad-index:rejected-before-consumption"

  let connectedExplicit ← runUnixCreate manager twoCandidateGlobal {inputs := #[]} (some ix2)
  unless connectedExplicit.machine.user.user.choices.cursor == 0 &&
      connectedExplicit.machine.user.user.choices.events.isEmpty &&
      (connectedExplicit.machine.dataRace.map fun global =>
        (global.vectorInfo[2]?, global.reuseCandidates)) == some (some child, [ix1]) do
    throw (IO.userError "UnixThread.create explicit clock override drew or changed behavior")
  IO.println "reuse:unix-thread-create:explicit-clock:no-draw"
