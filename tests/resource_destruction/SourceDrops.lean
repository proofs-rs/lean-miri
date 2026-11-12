import Miri.Input.EvalSourceOtherDestruction

open Miri.Memory Miri.Interpreter Miri.Concurrency
open Miri.Input.EvalSourceOtherDestruction

private abbrev O := SourceOther.Value Unit Unit Unit Unit
private abbrev D := Files.Description Nat Nat O
private abbrev F := Files.Ref D
private structure User where
  files : Files.Table D := {}
  ownership : FileOwnership.Registry D := {}
  readiness : ReadinessMachine.Registry F := {}
  sockets : SocketMachine.Registry Unit Unit Unit Unit := {}
  events : Array (Files.FdId × EventFd.Event) := #[]
  effects : Array String := #[]
  failSocketPut : Bool := false
private abbrev S := MachineHooks.State Unit User
private abbrev M := MachineHooks.M Unit User
private def initial (user : User) : S := {
  stack := Stack.empty
  machine := {
    memory := MemoryState.empty
    borrowTracker := none
    dataRace := none
    threads := ThreadManager.initial false
    raceAllocations := #[]
    allocationSpans := #[]
    user } }
private def fd (id : Nat) (value : D) : F := ⟨⟨id⟩,value⟩
private instance : Inhabited F := ⟨fd 0 .stdin⟩
private def virtual (id peer : Nat) (bytes : Array UInt8 := #[]) : Files.FdId × VirtualSocket.State :=
  (⟨id⟩,{readbuf := some ⟨⟨bytes⟩,.default⟩, peer := some ⟨⟨peer⟩⟩, nonblock := false, kind := .socketpair})
private def note (text : String) : M Unit :=
  modify fun state => {state with machine := {state.machine with user :=
    {state.machine.user with effects := state.machine.user.effects.push text}}}
private def resources : Resources S Nat Nat O := {
  dropFile := fun n => do note s!"file:{n}"; throw (.unsupported "host file cleanup")
  dropDirectory := fun n => do note s!"directory:{n}"; throw (.unsupported "host directory cleanup")
  dropOther := fun _ => do note "host-other"; throw (.unsupported "host Other-resource cleanup") }
private def files : FileMachine.Hooks Unit User Nat Nat O := {
  table := User.files, setTable := fun value user => {user with files := value}
  ownership := User.ownership, setOwnership := fun value user => {user with ownership := value}
  hostUsizeBits := 64, referenceBudget := 32
  onLastDrop := fun value => note (match value with | .file n _ _ => s!"legacy:{n}" | _ => "legacy") }
private def machine : ReadinessMachine.Hooks Unit User Nat Nat O := {
  files, registry := User.readiness, setRegistry := fun value user => {user with readiness := value}
  watcherReferenceBudget := 32
  onLastDrop := fun ref => files.onLastDrop ref.value }
private def context : Context Unit User Nat Nat Unit Unit Unit Unit := {
  machine, resources
  sockets := {
    get := fun user => .ok user.sockets
    put := fun value user =>
      if user.failSocketPut then .error (.unsupported "injected socket store failure")
      else .ok {user with sockets := value} }
  events := {
    get := User.events, put := fun value user => {user with events := value}
    tag := SourceOther.eventTag, untag := SourceOther.eventProject } }
private def bound := bind context
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def success (result : EStateM.Result StepError S Unit) : IO S :=
  match result with | .ok _ state => pure state | .error error _ => throw (IO.userError s!"unexpected failure: {reprStr error}")
private def failure (result : EStateM.Result StepError S Unit) (fragment : String) : IO S :=
  match result with
  | .error error state => do
    check (((reprStr error).splitOn fragment).length > 1) s!"wrong failure: {reprStr error}"
    pure state
  | .ok _ _ => throw (IO.userError "missing required failure")
private def strong (state : S) (id : Nat) : Nat :=
  ((state.machine.user.ownership.entries.find? (·.ref.id == ⟨id⟩)).map (·.strong)).getD 0
private def peerLost (state : S) : Bool :=
  ((state.machine.user.sockets.virtual.find? (·.1 == ⟨1⟩)).map (·.2.peerLostData)).getD false
private def pair (bytes : Array UInt8 := #[1]) (count : Nat := 1) : User := {
  ownership := ⟨#[⟨fd 0 (.other (.virtualSocket ⟨0⟩)),count⟩,⟨fd 1 (.other (.virtualSocket ⟨1⟩)),1⟩]⟩
  readiness := {watched := #[(⟨0⟩,{}),(⟨1⟩,{})]}
  sockets := {virtual := #[virtual 0 1 bytes,virtual 1 0]} }

-- The opt-in callback cannot change the legacy default callback computation.
private theorem legacy_callback (h : FileMachine.Hooks Unit User Nat Nat O) (ref : F)
    (legacy : h.onLastDropWithId = none) :
    FileMachine.destroyReference h ref = h.onLastDrop ref.value := by
  simp only [FileMachine.destroyReference, legacy]

private def checkVirtual : IO Unit := do
  let reference := fd 0 (.other (.virtualSocket ⟨0⟩))
  let retained ← success (FileMachine.dropReference bound.files reference (initial (pair #[1] 2)))
  check (strong retained 0 == 1 && !peerLost retained && retained.machine.user.readiness.delayed.isEmpty)
    "nonlast release ran destructor"
  let closed ← success (ReadinessMachine.dropFd bound reference retained)
  check (strong closed 0 == 0 && strong closed 1 == 2 && peerLost closed) "last-drop peer state/refcount"
  check (closed.machine.user.sockets.virtual.size == 1 && closed.machine.user.readiness.watched.size == 1)
    "source socket/watched state was not removed"
  check (closed.machine.user.readiness.delayed.size == 1 && closed.machine.user.readiness.delayed[0]!.id == ⟨1⟩)
    "close did not transfer the real peer reference to delayed readiness"
  -- Processing a delayed owned reference eventually releases its retain.
  let consumed := {closed with machine := {closed.machine with user := {closed.machine.user with
    readiness := {closed.machine.user.readiness with delayed := #[]}}}}
  let consumed ← success (FileMachine.dropReference bound.files (fd 1 (.other (.virtualSocket ⟨1⟩))) consumed)
  check (strong consumed 1 == 1) "delayed reference retain was lost or duplicated"
  let empty ← success (FileMachine.dropReference bound.files reference (initial (pair #[])))
  check (!peerLost empty && empty.machine.user.readiness.delayed.size == 1) "empty close lost notification"
  let deadPeer := {pair with ownership := ⟨#[⟨reference,1⟩]⟩}
  let dead ← success (FileMachine.dropReference bound.files reference (initial deadPeer))
  check (dead.machine.user.readiness.delayed.isEmpty) "dead peer was resurrected"
  -- Both outer release APIs must use the real payload, not a caller's forged value.
  let forged := fd 0 (.other (.eventFd ⟨99⟩))
  for drop in [FileMachine.dropReference bound.files, ReadinessMachine.dropFd bound] do
    let state ← success (drop forged (initial pair))
    check (peerLost state && state.machine.user.events.isEmpty) "released actual payload was discarded"

private def checkFailures : IO Unit := do
  let reference := fd 0 (.other (.virtualSocket ⟨0⟩))
  let bad := {pair with ownership := ⟨#[⟨fd 0 (.other (.virtualSocket ⟨7⟩)),1⟩]⟩}
  let state ← failure (FileMachine.dropReference bound.files reference (initial bad)) "identity mismatch"
  check (strong state 0 == 0 && state.machine.user.sockets.virtual.size == 2) "identity failure prefix changed"
  let noWatch := {pair with readiness := {watched := #[(⟨1⟩,{})]}}
  let state ← failure (ReadinessMachine.dropFd bound reference (initial noWatch)) "destroyed watched"
  check (strong state 0 == 0 && strong state 1 == 2 && peerLost state &&
    state.machine.user.readiness.delayed.size == 1 && state.machine.user.sockets.virtual.size == 2)
    "watched failure rolled back or reordered source peer/store effects"
  let state ← failure (FileMachine.dropReference bound.files reference (initial {pair with failSocketPut := true}))
    "injected socket store failure"
  check (strong state 0 == 0 && strong state 1 == 1 && !peerLost state &&
    state.machine.user.readiness.delayed.isEmpty && state.machine.user.sockets.virtual.size == 2)
    "failed peer update did not drop its temporary retained peer"
  let missing := {pair with sockets := {virtual := #[virtual 1 0]}}
  let state ← failure (FileMachine.dropReference bound.files reference (initial missing)) "virtual socket state"
  check (strong state 0 == 0) "missing source state resurrected ownership"
  let closed ← success (FileMachine.dropReference bound.files reference (initial pair))
  let _ ← failure (FileMachine.dropReference bound.files reference closed) "absent/ambiguous"
  pure ()

private def key (id : Nat) (number : Int32) : Readiness.Key := ⟨⟨id⟩,number⟩
private def interest (id : Nat) : Readiness.Interest := ⟨⟨⟨id⟩⟩,{},false,0,{}⟩
private def checkEventEpoll : IO Unit := do
  let event := fd 0 (.other (.eventFd ⟨0⟩))
  let watcher : Readiness.Watcher := {
    interests := #[(key 0 3,interest 0),(key 0 4,interest 0),(key 1 5,interest 1)]
    ready := #[key 0 3,key 0 4,key 1 5] }
  let user : User := {
    ownership := ⟨#[⟨event,1⟩,⟨fd 1 (.other (.virtualSocket ⟨1⟩)),1⟩]⟩
    readiness := {watchers := #[⟨7,1,watcher⟩],watched := #[(⟨0⟩,{watchers := #[7]}),(⟨1⟩,{})]}
    events := #[(⟨0⟩,⟨0,false,.default,#[],#[]⟩)] }
  let state ← success (FileMachine.dropReference bound.files event (initial user))
  check (state.machine.user.events.isEmpty && state.machine.user.readiness.watched.size == 1)
    "event source store/watched cleanup missing"
  let some live := state.machine.user.readiness.watchers[0]? | throw (IO.userError "watcher lost")
  check (live.strong == 1 && live.value.interests.size == 1 && live.value.ready.size == 1)
    "event drop retained an alias interest or dropped a live watcher"
  let _ ← failure (FileMachine.dropReference bound.files event (initial {user with readiness := {}})) "destroyed watched"
  let epoll := fd 0 (.other (.epoll 7))
  let watcher := {watcher with interests := #[(key 1 5,interest 1)],ready := #[key 1 5]}
  for count in [1,2] do
    let user := {user with
      ownership := ⟨#[⟨epoll,1⟩,⟨fd 1 (.other (.virtualSocket ⟨1⟩)),1⟩]⟩
      readiness := {watchers := #[⟨7,count,watcher⟩],watched := #[(⟨1⟩,{watchers := #[7]})]}}
    let state ← success (ReadinessMachine.dropFd bound epoll (initial user))
    check (strong state 0 == 0 && strong state 1 == 1) "epoll FD/temporary reference ownership changed"
    let some watched := state.machine.user.readiness.watched[0]? | throw (IO.userError "epoll lost watched metadata")
    if count == 1 then
      check (state.machine.user.readiness.watchers.isEmpty && watched.2.watchers.isEmpty)
        "epoll watcher field drop did not clean weak metadata"
    else
      let some retained := state.machine.user.readiness.watchers[0]? | throw (IO.userError "epoll lost retained watcher")
      check (retained.strong == 1 && watched.2.watchers == #[7]) "epoll released a still-owned watcher"

private def checkHostAndLegacy : IO Unit := do
  for value in [Files.Description.file 7 true true, Files.Description.directory 8, Files.Description.other (.tcpSocket ⟨0⟩),
      Files.Description.other (.dynamicSymbol "x"), Files.Description.other (.tcpState {socket := .initial (),family := .ipv4,nonblock := false})] do
    let reference := fd 0 value
    let state ← failure (FileMachine.dropReference bound.files reference
      (initial {ownership := ⟨#[⟨reference,1⟩]⟩})) "cleanup"
    check (strong state 0 == 0 && state.machine.user.effects.size == 1) "host failure was bypassed/rolled back"
  let actual := fd 0 (.file 7 true true)
  let forged := fd 0 (.file 99 true true)
  let start := initial {ownership := ⟨#[⟨actual,1⟩]⟩}
  let state ← success (FileMachine.dropReference files forged start)
  check (state.machine.user.effects == #["legacy:7"]) "legacy FileMachine callback changed"
  let state ← success (ReadinessMachine.dropFd machine forged start)
  check (state.machine.user.effects == #["legacy:99"]) "legacy readiness callback argument changed"

def main : IO Unit := do
  checkVirtual
  checkFailures
  checkEventEpoll
  checkHostAndLegacy
  IO.println "source resource destruction: last refs, peer ownership, delayed notification, watches, epoll, identities, failures and legacy/host boundaries passed"
