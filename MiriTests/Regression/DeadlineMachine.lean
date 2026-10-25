import Miri.Interpreter.DeadlineMachine

open Miri.Interpreter
open Miri.Interpreter.DeadlineMachine
open Miri.Concurrency
open Miri.Memory

namespace Deadline141QA

structure UserState where
  deadlines : Registry Nat Nat := Registry.empty
  clock : Clock.Monotonic Nat := .virtual 0
  callbackCount : Nat := 0


def freshDeadline : Clock.Deadline Nat Nat :=
  .monotonic (.virtual 0)

def token0 : ThreadDeadline := .Monotonic 0

def id0 : ThreadId := ThreadId.MAIN_THREAD

def id1 : ThreadId := ThreadId.ofU32 1 (by decide)

def mkRecord (state : ThreadState) : ThreadRecord :=
  { (ThreadRecord.initial none none) with state := state }

def managerWith (states : List (ThreadState × Nat)) : ThreadManager :=
  let main := ThreadRecord.initial (some [109,97,105,110]) none
  { ThreadManager.initial false with
    threads := main :: states.map (fun (state, callback) => mkRecord
      (match state with
       | .Blocked reason deadline _ => .Blocked reason deadline callback
       | state => state)) }

def baseUser (tokens : List Nat := [0]) : UserState :=
  { deadlines := {
      nextToken := (tokens.foldl max 0) + 1
      entries := tokens.foldl (fun entries token =>
        entries.insert token #[freshDeadline]) ({} : Std.HashMap Nat (Array (Clock.Deadline Nat Nat))) } }

def mkState (user : UserState) (threads : ThreadManager) : MachineHooks.State Miri.TreeBorrows.BorrowTree UserState :=
  { stack := Miri.Interpreter.Stack.empty
    machine := {
      memory := MemoryState.empty
      borrowTracker := none
      dataRace := none
      threads
      raceAllocations := #[]
      allocationSpans := #[]
      user } }

def hooks (reblockToken : Option Nat := none) : Hooks Miri.TreeBorrows.BorrowTree UserState Nat Nat :=
  let host : Clock.HostHooks Nat Nat
      (MachineHooks.State Miri.TreeBorrows.BorrowTree UserState) := {
    monotonicNow := pure 0
    systemNow := pure 0
    unixEpoch := 0
    checkedAddMonotonic := fun value _ => pure (some value)
    checkedAddSystem := fun value _ => pure (some value)
    durationSince := fun _ _ => pure ⟨0,0,by decide⟩
    sleep := fun _ => pure () }
  { registry := fun user => user.deadlines
    setRegistry := fun registry user => { user with deadlines := registry }
    clock := fun user => user.clock
    host
    communicate := pure false
    systemDurationSince := fun _ _ => pure none
    selectThread := fun id => do
      let state ← get
      match state.machine.threads.setActiveThread id with
      | .error _ => throw (.invalidProgram "QA select thread failed")
      | .ok (threads, previous) =>
        modify fun state => { state with machine := { state.machine with threads } }
        pure previous
    invokeCallback := fun callback _ => do
      modify fun state => { state with machine := { state.machine with
        user := { state.machine.user with callbackCount := state.machine.user.callbackCount + 1 } } }
      if let some token := reblockToken then
        if callback == 10 then
          let current ← get
          let updatedThreads := List.set current.machine.threads.threads 1
            (mkRecord (.Blocked .Semaphore (some (.Monotonic token)) callback))
          modify fun current => { current with machine := { current.machine with
            threads := { current.machine.threads with threads := updatedThreads } } }
      if callback == 20 then throw (.callback "deadline QA injected callback failure") }

def expiredThreads (callbacks : List Nat) : ThreadManager :=
  managerWith (callbacks.map fun callback => (.Blocked .Sleep (some token0) callback, callback))

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def registryChecks : IO Unit := do
  let empty : Registry Nat Nat := .empty
  check (match empty.lookup token0 with | .error (.invalidProgram "missing actual deadline") => true | _ => false) "missing lookup"
  let emptyRows : Registry Nat Nat := { nextToken := 1, entries := ({} : Std.HashMap Nat (Array (Clock.Deadline Nat Nat))).insert 0 #[] }
  check (match emptyRows.lookup token0 with | .error (.invalidProgram "missing actual deadline") => true | _ => false) "empty lookup"
  let duplicate : Registry Nat Nat := { nextToken := 1, entries := ({} : Std.HashMap Nat (Array (Clock.Deadline Nat Nat))).insert 0 #[freshDeadline, freshDeadline] }
  check (match duplicate.lookup token0 with | .error (.invalidProgram "ambiguous actual deadline") => true | _ => false) "duplicate lookup"
  let wrongClock : Registry Nat Nat := { nextToken := 1, entries := ({} : Std.HashMap Nat (Array (Clock.Deadline Nat Nat))).insert 0 #[.realTime 0] }
  check (match wrongClock.lookup token0 with | .error (.invalidProgram "deadline token clock-kind mismatch") => true | _ => false) "wrong clock lookup"
  let collision : Registry Nat Nat := { nextToken := 0, entries := ({} : Std.HashMap Nat (Array (Clock.Deadline Nat Nat))).insert 0 #[freshDeadline] }
  check (match collision.intern freshDeadline with | .error (.invalidProgram "deadline registry token collision") => true | _ => false) "collision"
  let (allocated, token) ← match (.empty : Registry Nat Nat).intern freshDeadline with
    | .error error => throw (IO.userError s!"intern: {reprStr error}")
    | .ok pair => pure pair
  let pruned := allocated.retain ({} : Std.HashSet Nat)
  let (afterPrune, nextToken) ← match pruned.intern freshDeadline with
    | .error error => throw (IO.userError s!"intern after prune: {reprStr error}")
    | .ok pair => pure pair
  check (token == .Monotonic 0 && nextToken == .Monotonic 1 && afterPrune.nextToken == 2) "monotone token after prune"

def sweepChecks : IO Unit := do
  let successState := mkState (baseUser [0]) (expiredThreads [30])
  match (unblockExpiredDeadlines (hooks)).run successState with
  | .error error _ => throw (IO.userError s!"success sweep errored: {reprStr error}")
  | .ok minimum state => do
    check (minimum == none) "success minimum wait"
    check (state.machine.threads.threads[1]?.map (·.state) == some .Enabled) "successful expiration enables thread"
    check (state.machine.user.deadlines.entries.isEmpty) "successful expiration prunes token"
    check (state.machine.threads.activeThread == id0) "successful callback restores active thread"

  let reblockState := mkState (baseUser [0]) (expiredThreads [10])
  match (unblockExpiredDeadlines (hooks (some 0))).run reblockState with
  | .error error _ => throw (IO.userError s!"reblock sweep errored: {reprStr error}")
  | .ok _ state => do
    check (state.machine.threads.threads[1]?.map (·.state) == some (.Blocked .Semaphore (some token0) 10)) "callback reblocks same token"
    check (state.machine.user.deadlines.entries.contains 0) "reblocked token retained"
    check (state.machine.threads.activeThread == id0) "reblock callback restores active thread"

  let errorState := mkState (baseUser [0,1]) (expiredThreads [20,30])
  match (unblockExpiredDeadlines (hooks)).run errorState with
  | .ok _ _ => throw (IO.userError "injected callback unexpectedly succeeded")
  | .error error state => do
    check (error == .callback "deadline QA injected callback failure") "callback error is preserved"
    let sweptThreads := expiredThreads [20,30]
    let expectedThreads := { sweptThreads with
      activeThread := id1
      threads := List.set (List.set sweptThreads.threads 1
        (mkRecord .Enabled)) 2 (mkRecord .Enabled) }
    check (reprStr state.machine.threads == reprStr expectedThreads) "callback error preserves exact thread-state prefix"
    check (state.machine.user.deadlines.entries.contains 0 && state.machine.user.deadlines.entries.contains 1 &&
      state.machine.user.deadlines.entries.size == 2 && state.machine.user.deadlines.nextToken == 2) "callback error skips pruning and preserves registry"
    check (state.machine.user.callbackCount == 1) "later callback skipped after first callback error"

def scopeChecks : IO Unit := do
  let getRegistry : UserState → Registry Nat Nat := fun user => user.deadlines
  let setRegistry : Registry Nat Nat → UserState → UserState :=
    fun registry user => { user with deadlines := registry }
  let emptyManager := managerWith []
  let waitingUser := baseUser [0]
  let waitingState := mkState waitingUser emptyManager
  let transient : EStateM StepError
      (MachineHooks.State Miri.TreeBorrows.BorrowTree UserState) Unit := do
    let _ ← unblockExpiredDeadlines (hooks)
    let state ← get
    if state.machine.user.deadlines.pruneDepth != 1 ||
        !(state.machine.user.deadlines.entries.contains 0) then
      throw (.invalidProgram "nested sweep pruned an on-stack deadline")
    let blocked := managerWith [(.Blocked .Condvar (some token0) 10, 10)]
    modify fun state => { state with machine := { state.machine with threads := blocked } }
  match (withPruneSuppressed getRegistry setRegistry transient).run waitingState with
  | .error error _ => throw (IO.userError s!"on-stack scope errored: {reprStr error}")
  | .ok _ state => do
    check (state.machine.user.deadlines.pruneDepth == 0) "on-stack scope depth not restored"
    check (state.machine.user.deadlines.entries.contains 0) "later blocked on-stack deadline was pruned"

  let readyThenTimeout := managerWith [
    (.Blocked .Semaphore (some token0) 10, 10),
    (.Blocked .Condvar (some (.Monotonic 1)) 30, 30)]
  let paired := mkState (baseUser [0,1]) readyThenTimeout
  let nested := withPruneSuppressed getRegistry setRegistry
    (unblockExpiredDeadlines (hooks (some 0)))
  match nested.run paired with
  | .error error _ => throw (IO.userError s!"nested callback batch errored: {reprStr error}")
  | .ok minimum state => do
    check (minimum == none) "nested callback batch minimum"
    check (state.machine.user.deadlines.pruneDepth == 0) "nested callback depth not restored"
    check (state.machine.user.deadlines.entries.contains 0) "nested Ready callback lost reblocked token"
    check (!(state.machine.user.deadlines.entries.contains 1)) "completed pending timeout token not pruned"
    check (state.machine.user.callbackCount == 2) "pending timeout callback count"

  let failed := mkState (baseUser [0,1]) (expiredThreads [20,30])
  let nestedFailure := withPruneSuppressed getRegistry setRegistry
    (unblockExpiredDeadlines (hooks))
  match nestedFailure.run failed with
  | .ok _ _ => throw (IO.userError "nested callback failure unexpectedly succeeded")
  | .error error state => do
    check (error == .callback "deadline QA injected callback failure") "nested callback error changed"
    check (state.machine.user.deadlines.pruneDepth == 0) "nested failure depth not restored"
    check (state.machine.user.deadlines.entries.contains 0 &&
        state.machine.user.deadlines.entries.contains 1) "nested error pruned registry prefix"
    check (state.machine.user.callbackCount == 1) "nested error executed later callback"

  check (match (Registry.empty : Registry Nat Nat).leavePruneSuppression {} with
    | .error (.invalidProgram "deadline prune-suppression depth underflow") => true
    | _ => false) "prune depth underflow accepted"

end Deadline141QA

open Deadline141QA

def main : IO Unit := do
  registryChecks
  sweepChecks
  scopeChecks
  IO.println "DeadlineMachine143 QA PASS"
