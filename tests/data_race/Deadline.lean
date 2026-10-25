import Miri.Concurrency

open Miri.Concurrency

private def reasonName : BlockReason → String
  | .Join _ => "Join"
  | .Sleep => "Sleep"
  | .Mutex => "Mutex"
  | .Condvar => "Condvar"
  | .RwLock => "RwLock"
  | .Semaphore => "Semaphore"
  | .Futex => "Futex"
  | .InitOnce => "InitOnce"
  | .Readiness => "Readiness"
  | .Eventfd => "Eventfd"
  | .VirtualSocket => "VirtualSocket"
  | .IO => "IO"

private def deadlineScenario : Except String (List String) := do
  let initial := ThreadManager.initial false
  let (created, first) ← (ThreadManager.createThread initial 1).mapError (fun _ => "create first")
  let (created, second) ← (ThreadManager.createThread created 2).mapError (fun _ => "create second")
  let (activeFirst, _) ← (ThreadManager.setActiveThread created first).mapError (fun _ => "active first")
  let activeFirst ← (ThreadManager.blockThreadWithRuntimeConstraints activeFirst
    .Mutex (some (.Monotonic 100)) 51 true).mapError (fun _ => "block first")
  let (activeSecond, _) ← (ThreadManager.setActiveThread activeFirst second).mapError (fun _ => "active second")
  let activeSecond ← (ThreadManager.blockThreadWithRuntimeConstraints activeSecond
    .Condvar (some (.RealTime 200)) 52 true).mapError (fun _ => "block second")
  let (manager, _) ← (ThreadManager.setActiveThread activeSecond ThreadId.MAIN_THREAD)
    |>.mapError (fun _ => "restore main")
  let sweep := DeadlineSweep.sweep manager [
    { thread := first, remaining := 0 }, { thread := second, remaining := 6 }] true
  let firstEnabled := (manager.thread? first).map ThreadRecord.isEnabled
  let afterSweepFirst := (sweep.manager.thread? first).map ThreadRecord.isEnabled
  let afterSweepSecond := (sweep.manager.thread? second).map ThreadRecord.isEnabled
  let sweepLine := s!"sweep:queued={sweep.callbacks.length}:minimum={sweep.minimumWait}:before={firstEnabled}:expired={afterSweepFirst}:future={afterSweepSecond}"
  let duplicateSweep := DeadlineSweep.sweep manager [
    { thread := first, remaining := 0 }, { thread := first, remaining := 8 },
    { thread := second, remaining := 6 }] true
  let duplicateRejected := match duplicateSweep.outcome with
    | some (.duplicateObservations thread) => thread == first
    | _ => false
  let duplicateUnchanged := (duplicateSweep.manager.thread? first).map fun thread =>
    match thread.state with | .Blocked .. => true | _ => false
  let duplicateLine := s!"duplicate:rejected={duplicateRejected}:unchanged={duplicateUnchanged}:queued={duplicateSweep.callbacks.length}"
  let callbackStep ← (ThreadManager.beginDeadlineCallbacks sweep)
    |>.mapError (fun _ => "begin callbacks")
  let callbackLine := match callbackStep with
    | .invoke _manager obligation remaining minimum =>
      s!"callback:target={obligation.target.toNat}:previous={obligation.previousActive.toNat}:reason={reasonName obligation.reason}:timedout={obligation.kind == .TimedOut}:token={obligation.callbackToken}:remaining={remaining.length}:minimum={minimum}"
    | _ => "callback:unexpected"
  let wrongKindRejected := match callbackStep with
    | .invoke manager obligation remaining minimum =>
      match ThreadManager.continueDeadlineCallbacks manager
          { obligation with kind := .Ready } remaining minimum true with
      | .error (.wrongCallbackKind .TimedOut .Ready) => true
      | _ => false
    | _ => false
  let wrongKindLine := s!"callback-kind-mismatch:rejected={wrongKindRejected}"
  let failedStep ← match callbackStep with
    | .invoke manager obligation remaining minimum =>
      (ThreadManager.continueDeadlineCallbacks manager obligation remaining minimum false)
        |>.mapError (fun _ => "callback failure")
    | _ => throw "missing timeout callback"
  let failureLine := match failedStep with
    | .callbackFailed manager _ remaining _ =>
      s!"callback-failure:active={manager.activeThread.toNat}:remaining={remaining.length}"
    | _ => "callback-failure:unexpected"

  let isolationBase := ThreadManager.initial false
  let mainBlocked ← (ThreadManager.blockThreadWithRuntimeConstraints isolationBase
    .Mutex (some (.Monotonic 1)) 61 true).mapError (fun _ => "block isolation main")
  let (withChild, child) ← (ThreadManager.createThread mainBlocked 2).mapError (fun _ => "isolation child")
  let (childActive, _) ← (ThreadManager.setActiveThread withChild child)
    |>.mapError (fun _ => "activate isolation child")
  let childBlocked ← (ThreadManager.blockThreadWithRuntimeConstraints childActive
    .Condvar (some (.RealTime 2)) 62 true).mapError (fun _ => "block isolation child")
  let (isolationManager, _) ← (ThreadManager.setActiveThread childBlocked ThreadId.MAIN_THREAD)
    |>.mapError (fun _ => "restore isolation main")
  let isolatedSweep := DeadlineSweep.sweep isolationManager [
    { thread := ThreadId.MAIN_THREAD, remaining := 0 }, { thread := child, remaining := 1 }] false
  let mainEnabled := (isolatedSweep.manager.thread? ThreadId.MAIN_THREAD).map ThreadRecord.isEnabled
  let childBlockedNow := (isolatedSweep.manager.thread? child).map fun thread =>
    match thread.state with | .Blocked .. => true | _ => false
  let isolationLine := s!"isolation-panic:main-expired={mainEnabled}:later-still-blocked={childBlockedNow}:queued={isolatedSweep.callbacks.length}:error={isolatedSweep.outcome.isSome}"
  pure [sweepLine, duplicateLine, callbackLine, wrongKindLine,
    failureLine, isolationLine]

def main : IO Unit := do
  match deadlineScenario with
  | .error error => IO.println s!"deadline:error:{error}"
  | .ok lines => for line in lines do IO.println line
