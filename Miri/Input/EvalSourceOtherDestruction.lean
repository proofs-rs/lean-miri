import Miri.Input.EvalSocketStorage
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.PollMachine

/-! Source-owned descriptor destruction uses only the canonical ownership,
protocol and readiness stores. Host resources retain their explicit effects;
no provisional I/O or protocol dictionary is captured by these callbacks. -/
namespace Miri.Input.EvalSourceOtherDestruction
open Miri.Memory Miri.Interpreter Files

structure Resources (S H D O : Type) where
  dropFile : H → EStateM StepError S Unit
  dropDirectory : D → EStateM StepError S Unit
  dropOther : O → EStateM StepError S Unit

structure Context (K U H D R L T E : Type) where
  machine : ReadinessMachine.Hooks K U H D (SourceOther.Value R L T E)
  sockets : SocketMachine.Store U R L T E
  events : EventFdMachine.Store U (SourceOther.Value R L T E)
  resources : Resources (MachineHooks.State K U) H D (SourceOther.Value R L T E)

private abbrev Ref (H D R L T E : Type) := Files.Ref (Description H D (SourceOther.Value R L T E))
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

private def getVirtual (c : Context K U H D R L T E) (ref : Ref H D R L T E) :
    MachineHooks.M K U VirtualSocket.State := do
  let entries := (← lift (c.sockets.get (← get).machine.user)).virtual.filter (·.1 == ref.id)
  if entries.size != 1 then throw (.invalidProgram "virtual socket state missing/ambiguous")
  let some (_,value) := entries[0]? | throw (.invalidProgram "virtual socket state missing")
  return value

private def putVirtual (c : Context K U H D R L T E) (ref : Ref H D R L T E)
    (value : VirtualSocket.State) : MachineHooks.M K U Unit := do
  let _ ← getVirtual c ref
  let state ← get
  let registry ← lift (c.sockets.get state.machine.user)
  let user ← lift (c.sockets.put {registry with virtual := registry.virtual.map fun (id,old) =>
    (id,if id == ref.id then value else old)} state.machine.user)
  set {state with machine := {state.machine with user}}

private def removeSocket (c : Context K U H D R L T E) (ref : Ref H D R L T E) : MachineHooks.M K U Unit := do
  let state ← get
  let registry ← lift (c.sockets.get state.machine.user)
  let user ← lift (c.sockets.put {registry with
    virtual := registry.virtual.filter (·.1 != ref.id)
    tcp := registry.tcp.filter (·.1 != ref.id)} state.machine.user)
  set {state with machine := {state.machine with user}}

private def removeWatched (c : Context K U H D R L T E) (ref : Ref H D R L T E) : MachineHooks.M K U Unit :=
  modify fun state =>
    let registry := c.machine.registry state.machine.user
    let user := c.machine.setRegistry {registry with watched := registry.watched.filter (·.1 != ref.id)} state.machine.user
    {state with machine := {state.machine with user}}

private def destruction (c : Context K U H D R L T E)
    (releaseFd : Ref H D R L T E → MachineHooks.M K U Unit)
    (releaseWatcher : Nat → MachineHooks.M K U Unit) :
    Readiness.DestructionHooks (MachineHooks.State K U) (Ref H D R L T E) :=
  ReadinessMachine.destructionViews c.machine releaseFd releaseWatcher

mutual
  /-- Rc destruction can release other owned references. Every release uses
  the real ownership registry; no fresh budget or successful fallback is used. -/
  partial def release (c : Context K U H D R L T E) (ref : Ref H D R L T E) : MachineHooks.M K U Unit := do
    let (ownership,last) ← lift (FileOwnership.release (c.machine.files.ownership (← get).machine.user) ref.id)
    modify fun state => {state with machine := {state.machine with user := c.machine.files.setOwnership ownership state.machine.user}}
    if let some value := last then destroyAndFinish c {ref with value}

  partial def releaseWatcher (c : Context K U H D R L T E) (id : Nat) : MachineHooks.M K U Unit :=
    ReadinessMachine.dropWatcherWith c.machine (destruction c (release c) (releaseWatcher c)) id

  /-- Ownership has already reached zero before this source destructor runs. -/
  partial def destroy (c : Context K U H D R L T E) (ref : Ref H D R L T E) : MachineHooks.M K U Unit := do
    match ref.value with
    | .stdin | .stdout | .stderr | .nullOutput => pure ()
    | .file handle _ _ => c.resources.dropFile handle
    | .directory handle => c.resources.dropDirectory handle
    | .other (.virtualSocket id) =>
      unless id == ref.id do throw (.invalidProgram "virtual socket payload/ownership identity mismatch")
      let hooks : VirtualSocket.DropHooks (MachineHooks.State K U) (Ref H D R L T E) := {
        upgrade := (destruction c (release c) (releaseWatcher c)).upgrade
        dropFd := release c
        get := getVirtual c
        put := putVirtual c
        addDelayed := fun peer => modify fun state =>
          let registry := c.machine.registry state.machine.user
          let user := c.machine.setRegistry {registry with delayed := registry.delayed.push peer} state.machine.user
          {state with machine := {state.machine with user}} }
      VirtualSocket.dropSocketWith hooks (← getVirtual c ref)
      ReadinessMachine.destroyWatchedWith c.machine (destruction c (release c) (releaseWatcher c)) ref
      removeSocket c ref
    | .other (.eventFd id) =>
      unless id == ref.id do throw (.invalidProgram "eventfd payload/ownership identity mismatch")
      EventFdMachine.dropEventWith c.events
        (ReadinessMachine.destroyWatchedWith c.machine (destruction c (release c) (releaseWatcher c))) ref
    | .other (.epoll watcher) => PollMachine.dropEpollWith (releaseWatcher c) ⟨watcher⟩
    | .other payload => c.resources.dropOther payload

  /-- FileMachine's ID-aware callback also owns watched-record removal.
  ReadinessMachine's route keeps that final removal in its original outer step. -/
  partial def destroyAndFinish (c : Context K U H D R L T E) (ref : Ref H D R L T E) : MachineHooks.M K U Unit := do
    destroy c ref
    match ref.value with
    | .other (.virtualSocket _) | .other (.eventFd _) => removeWatched c ref
    | _ => pure ()
end

/-- Bind both last-owner routes to the same canonical stores. The old host
callbacks remain the fallback for true host resources and unsupported tags. -/
def bind (c : Context K U H D R L T E) : ReadinessMachine.Hooks K U H D (SourceOther.Value R L T E) :=
  {c.machine with
    files := {c.machine.files with onLastDropWithId := some (destroyAndFinish c)}
    onLastDrop := destroy c}

end Miri.Input.EvalSourceOtherDestruction
