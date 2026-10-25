import Miri.Concurrency.GlobalState

/-! Draft source-level lifecycle witness for the pinned release/join ordering.
It is intentionally not executed during the active source134 full build. It
uses no hand-seeded candidate clocks: creation, termination, join and the next
creation all call the ordinary GlobalState/ThreadManager transitions. -/
open Miri.Concurrency

private def mustThread {α : Type} (value : Except ThreadError α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError (reprStr error))

private def mustGlobal {α : Type} (value : Except GlobalStateError α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError (reprStr error))

def main : IO Unit := do
  let zero := VectorIdx.ofU32 0 (by decide)
  let one := VectorIdx.ofU32 1 (by decide)
  let base := GlobalState.initial false false
  let manager := ThreadManager.initial false

  -- First source thread creation: create the manager record, then the matching
  -- global clock entry while the parent remains active.
  let (manager, first) ← mustThread (ThreadManager.createThread manager 1)
  let afterCreate ← mustGlobal (GlobalState.threadCreated base manager first none)
  unless afterCreate.vectorInfo[0]? == some ThreadId.MAIN_THREAD &&
      afterCreate.vectorInfo[1]? == some first do
    throw (IO.userError "first creation did not assign fresh vector index 1")

  -- Source termination runs after TLS cleanup, marks the child Terminated,
  -- captures the old clock through release_clock, then increments its own tick.
  let (childActive, _) ← mustThread (ThreadManager.setActiveThread manager first)
  let some record := childActive.thread? first | throw (IO.userError "missing first thread")
  let terminatedManager := { childActive with
    threads := childActive.threads.set first.toNat { record with state := .Terminated } }
  let afterTermination ← mustGlobal (GlobalState.threadTerminated afterCreate terminatedManager)
  let some extra := afterTermination.threadInfo[first.toNat]? | throw (IO.userError "missing first thread metadata")
  let some snapshot := extra.terminationVectorClock | throw (IO.userError "termination snapshot missing")
  let some terminatedClock := afterTermination.vectorClocks[one.toNat]? | throw (IO.userError "terminated clock missing")
  unless (snapshot.index one).time == 1 &&
      (terminatedClock.clock.index one).time == 2 do
    throw (IO.userError "release callback must snapshot before its final increment")

  -- Successful join acquires the saved snapshot, not the post-callback clock.
  let (parentActive, _) ← mustThread (ThreadManager.setActiveThread terminatedManager ThreadId.MAIN_THREAD)
  let joinedManager ← mustThread (ThreadManager.markJoined parentActive first)
  let afterJoin ← mustGlobal (GlobalState.threadJoined afterTermination joinedManager first)
  let some parentClock := afterJoin.vectorClocks[zero.toNat]? | throw (IO.userError "parent clock missing")
  unless (parentClock.clock.index one).time == (snapshot.index one).time do
    throw (IO.userError "join acquired a different clock than the stored termination snapshot")
  unless GlobalState.reusableCandidates afterJoin == [] do
    throw (IO.userError "a terminated index unexpectedly passed the live-parent safety check")

  -- The next creation receives a fresh index; the old index remains in the
  -- source candidate set but is filtered out before the choice hook is called.
  let (manager, second) ← mustThread (ThreadManager.createThread joinedManager 2)
  let afterSecondCreate ← mustGlobal (GlobalState.threadCreated afterJoin manager second none)
  let some secondExtra := afterSecondCreate.threadInfo[second.toNat]?
    | throw (IO.userError "missing second thread metadata")
  unless secondExtra.vectorIndex == some (VectorIdx.ofU32 2 (by decide)) do
    throw (IO.userError "second source thread reused an unsafe terminated clock")
  IO.println "thread-clock-reuse:post-release-tick-unpublished:no-safe-candidate:fresh-index-2"
