import Miri.Concurrency.Thread

open Miri.Concurrency

private def callbackScenario : Except ThreadError String := do
  let manager := ThreadManager.initial false
  let (withChild, child) ← ThreadManager.createThread manager 11
  let (onChild, _) ← ThreadManager.setActiveThread withChild child
  let blocked ← ThreadManager.blockThread onChild .Sleep none 88
  let (onMain, _) ← ThreadManager.setActiveThread blocked ThreadId.MAIN_THREAD
  let (unblocked, callback) ← ThreadManager.unblockThread onMain child .Sleep
  let reason := match callback.reason with
    | .Sleep => "Sleep"
    | .Join _ => "Join"
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
  pure s!"callback:pending:active={unblocked.activeThread.toNat}:target={callback.target.toNat}:previous={callback.previousActive.toNat}:token={callback.callbackToken}:reason={reason}"

private def terminationScenario : Except ThreadTerminationError String := do
  let manager := ThreadManager.initial false
  let (withChild, child) ← (ThreadManager.createThread manager 12).mapError
    ThreadTerminationError.threadError
  let blockedJoiner ← (ThreadManager.blockThread withChild (.Join child) none 91).mapError
    ThreadTerminationError.threadError
  let (onChild, _) ← (ThreadManager.setActiveThread blockedJoiner child).mapError
    ThreadTerminationError.threadError
  let onChild := { onChild with threadLocalAllocs := [
    { definitionToken := 7, thread := child, pointerToken := 55 }] }
  let (terminated, obligation) ← ThreadManager.beginTerminateActive onChild true .Ready
  let cleanupAction := match obligation.tlsCleanup with
    | [cleanup] => s!"retain-{cleanup.pointerToken}"
    | _ => "invalid-cleanup-obligation"
  let failed := ThreadManager.completeTlsCleanup terminated obligation [.Failed 55]
  let failureCode := match failed with
    | .error (.cleanupResultMismatch _ (.Failed _)) => "failure:hook-blocked"
    | .error _ => "failure:other-error"
    | .ok _ => "failure:unexpected-hook"
  let continuation ← ThreadManager.completeTlsCleanup terminated obligation
    [.RetainedAsStaticRoot 55]
  let waiters := String.intercalate ","
    (continuation.joinWaiters.map fun id => toString id.toNat)
  pure s!"tls:{cleanupAction}:ready:{failureCode}:hook={continuation.dataRaceHookThread.toNat}:waiters={waiters}"

def main : IO Unit := do
  match callbackScenario with
  | .error _ => IO.println "callback:error"
  | .ok line => IO.println line
  match terminationScenario with
  | .error _ => IO.println "termination:error"
  | .ok line => IO.println line
