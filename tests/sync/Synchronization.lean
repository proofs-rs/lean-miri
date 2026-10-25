import Miri.Concurrency.Sync

open Miri.Concurrency

private def remoteClock : VClock :=
  VClock.newWithIndex (VectorIdx.ofU32 1 (by decide))
    (VTimestamp.ofPacked 6 (by decide))

private def clockAt (state : GlobalState) (index : Nat) : Option Nat :=
  match state.vectorClocks.head? with
  | none => none
  | some clocks =>
    match VectorIdx.ofNat index with
    | .error _ => none
    | .ok index => some (clocks.clock.index index).time

def main : IO Unit := do
  let manager := ThreadManager.initial false
  let global := GlobalState.initial true false
  let first := MutexState.lock { clock := remoteClock } global manager .vectorClocks
  let second := MutexState.lock first.syncState first.global manager .vectorClocks
  let output := s!"sync:mutex-lock owner={reprStr (first.syncState.owner.map ThreadId.toNat)} count={second.syncState.lockCount} acquired={reprStr (clockAt second.global 1)}"
  IO.println output

  let afterInnerUnlock := MutexState.unlock second.syncState second.global manager .vectorClocks
  let afterOuterUnlock := MutexState.unlock afterInnerUnlock.syncState
    afterInnerUnlock.global manager .vectorClocks
  IO.println s!"sync:mutex-reentrant-unlock inner={afterInnerUnlock.syncState.lockCount} owner-after-outer={reprStr (afterOuterUnlock.syncState.owner.map ThreadId.toNat)}"

  let (withChild, child) ← match ThreadManager.createThread manager 77 with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok created => pure created
  let globalWithChild ← match GlobalState.threadCreated global withChild child none with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok updated => pure updated
  let childManager ← match ThreadManager.setActiveThread withChild child with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let enqueued := MutexState.enqueueAndBlock
    { owner := some ThreadId.MAIN_THREAD, lockCount := 1 }
    globalWithChild childManager 901
  let mainManager ← match ThreadManager.setActiveThread enqueued.threads ThreadId.MAIN_THREAD with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let unlocked := MutexState.unlock enqueued.syncState enqueued.global mainManager
    .vectorClocks enqueued.callbackRegistration.toList
  IO.println s!"sync:mutex-wakeup callback={reprStr unlocked.callback} active={unlocked.threads.activeThread.toNat} queued={unlocked.syncState.queue.length} prev={mainManager.activeThread.toNat}"
  match unlocked.callback with
  | none => IO.println "sync:mutex-callback:missing"
  | some callback =>
    let finished := finishMutexAcquireCallback unlocked.syncState unlocked.global
      unlocked.threads callback .vectorClocks (MutexUnlockResult.returnedSome 1)
    IO.println s!"sync:mutex-callback:result={reprStr finished.outcome} owner={reprStr (finished.syncState.owner.map ThreadId.toNat)} active={finished.threads.activeThread.toNat} child-enabled={reprStr ((finished.threads.thread? child).map ThreadRecord.isEnabled)}"

  let reader := RwLockState.readerLock {} global manager .vectorClocks
  let readerReleased := RwLockState.readerUnlock reader.syncState reader.global manager .vectorClocks
  IO.println s!"sync:rwlock-reader-unlock result={reprStr readerReleased.outcome} locked={readerReleased.syncState.isLocked} released={reprStr (clockAt readerReleased.global 0)}"

  let writer := RwLockState.writerLock {} global manager .vectorClocks
  let writerReleased := RwLockState.writerUnlock writer.syncState writer.global manager .vectorClocks
  IO.println s!"sync:rwlock-writer-unlock result={reprStr writerReleased.outcome} locked={writerReleased.syncState.isLocked}"

  let (withWaiter, waiter) ← match ThreadManager.createThread manager 88 with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok created => pure created
  let clocksWithWaiter ← match GlobalState.threadCreated global withWaiter waiter none with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok updated => pure updated
  let waiterActive ← match ThreadManager.setActiveThread withWaiter waiter with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated

  let condvarWait := CondvarState.blockAfterMutexUnlock {} clocksWithWaiter waiterActive
    (.returnedSome 1) none 700 710 711 712 713 true
  let condvarMain ← match ThreadManager.setActiveThread condvarWait.threads ThreadId.MAIN_THREAD with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let some condvarRegistration := condvarWait.callbackRegistration
    | IO.println "sync:test-setup-error:missing-condvar-callback-registration"
      return
  let condvarSignal := CondvarState.signal condvarWait.syncState condvarWait.global
    condvarMain .vectorClocks [condvarRegistration]
  IO.println s!"sync:condvar-signal pending={reprStr (condvarSignal.callback.map (fun callback => callback.program))} active={condvarSignal.threads.activeThread.toNat} waiters={condvarSignal.syncState.waiters.length}"
  let some condvarCallback := condvarSignal.callback
    | IO.println "sync:test-setup-error:missing-condvar-callback"
      return
  let condvarReacquire := CondvarState.finishWaitCallback condvarSignal.syncState {}
    condvarSignal.global condvarSignal.threads condvarCallback .vectorClocks 710 714
  IO.println s!"sync:condvar-reacquire callback={reprStr (condvarReacquire.callback.map (fun callback => callback.program))} mutex-owner={reprStr (condvarReacquire.syncState.2.owner.map ThreadId.toNat)} active={condvarReacquire.threads.activeThread.toNat}"
  let some scalarWrite := condvarReacquire.callback
    | IO.println "sync:test-setup-error:missing-condvar-write"
      return
  let condvarReturned := finishScalarWriteCallback condvarReacquire.syncState
    condvarReacquire.global condvarReacquire.threads scalarWrite true
  IO.println s!"sync:condvar-return active={condvarReturned.threads.activeThread.toNat} result={reprStr condvarReturned.outcome}"
  let condvarBlockedOnMutex := CondvarState.finishWaitCallback condvarSignal.syncState
    { owner := some ThreadId.MAIN_THREAD, lockCount := 1 }
    condvarSignal.global condvarSignal.threads condvarCallback .vectorClocks 710 715
  IO.println s!"sync:condvar-mutex-block registered={reprStr condvarBlockedOnMutex.callbackRegistration} waiter={reprStr ((condvarBlockedOnMutex.threads.thread? waiter).map (fun thread => thread.state))} active={condvarBlockedOnMutex.threads.activeThread.toNat}"
  let some mutexCallbackRegistration := condvarBlockedOnMutex.callbackRegistration
    | IO.println "sync:test-setup-error:missing-condvar-mutex-registration"
      return
  let condvarMutexUnlock := MutexState.unlock condvarBlockedOnMutex.syncState.2
    condvarBlockedOnMutex.global condvarBlockedOnMutex.threads .vectorClocks
    [mutexCallbackRegistration]
  let some mutexWriteCallback := condvarMutexUnlock.callback
    | IO.println "sync:test-setup-error:missing-condvar-mutex-wakeup"
      return
  let condvarMutexAcquired := finishMutexAcquireAndWriteCallback
    condvarMutexUnlock.syncState condvarMutexUnlock.global condvarMutexUnlock.threads
    mutexWriteCallback .vectorClocks
  IO.println s!"sync:condvar-mutex-callback write={reprStr (condvarMutexAcquired.callback.map (fun callback => callback.program))} owner={reprStr (condvarMutexAcquired.syncState.owner.map ThreadId.toNat)} active={condvarMutexAcquired.threads.activeThread.toNat}"
  let some condvarMutexScalarWrite := condvarMutexAcquired.callback
    | IO.println "sync:test-setup-error:missing-condvar-mutex-write"
      return
  let condvarMutexReturned := finishScalarWriteCallback condvarMutexAcquired.syncState
    condvarMutexAcquired.global condvarMutexAcquired.threads condvarMutexScalarWrite true
  IO.println s!"sync:condvar-mutex-return active={condvarMutexReturned.threads.activeThread.toNat}"

  let rwReaderWait := RwLockState.enqueueReaderAndBlock
    { writer := some ThreadId.MAIN_THREAD }
    clocksWithWaiter waiterActive 720 721 722
  let rwWriterMain ← match ThreadManager.setActiveThread rwReaderWait.threads ThreadId.MAIN_THREAD with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let rwWriterUnlock := RwLockState.writerUnlock rwReaderWait.syncState
    rwReaderWait.global rwWriterMain .vectorClocks rwReaderWait.callbackRegistration.toList
  let some rwReadCallback := rwWriterUnlock.callback
    | IO.println "sync:test-setup-error:missing-rwlock-reader-callback"
      return
  let rwReadAcquired := finishRwLockAcquireCallback rwWriterUnlock.syncState
    rwWriterUnlock.global rwWriterUnlock.threads rwReadCallback .vectorClocks
  IO.println s!"sync:rwlock-wake-readers={reprStr (rwReadAcquired.callback.map (fun callback => callback.program))} reader-count={reprStr (rwReadAcquired.syncState.readers)}"
  let some rwScalarWrite := rwReadAcquired.callback
    | IO.println "sync:test-setup-error:missing-rwlock-scalar-write"
      return
  let rwCallbackReturned := finishScalarWriteCallback rwReadAcquired.syncState
    rwReadAcquired.global rwReadAcquired.threads rwScalarWrite true
  IO.println s!"sync:rwlock-callback-return active={rwCallbackReturned.threads.activeThread.toNat}"

  let (futexThreads, futexThread) ← match ThreadManager.createThread manager 89 with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok created => pure created
  let futexGlobal ← match GlobalState.threadCreated global futexThreads futexThread none with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok updated => pure updated
  let futexActive ← match ThreadManager.setActiveThread futexThreads futexThread with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let futexWait := FutexState.wait {} futexGlobal futexActive (UInt32.ofNat 1)
    none 800 801 true
  let timedOutManager ← match futexWait.threads.unblockThread futexThread .Futex .TimedOut with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let timeoutRequest : SyncCallbackRequest := {
    unblock := {
      target := futexThread
      previousActive := ThreadId.MAIN_THREAD
      reason := .Futex
      callbackToken := 800
      kind := .TimedOut }
    program := (.futexWait 801) }
  let timeoutCallback := FutexState.finishWaitCallback futexWait.syncState futexWait.global
    timedOutManager timeoutRequest .none
  IO.println s!"sync:futex-timeout waiters={timeoutCallback.syncState.waiterCount} pending={reprStr (timeoutCallback.callback.map (fun callback => callback.program))} active={timeoutCallback.threads.activeThread.toNat}"
  let futexMain ← match ThreadManager.setActiveThread futexWait.threads ThreadId.MAIN_THREAD with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let futexRegistry := futexWait.callbackRegistration.toList
  let wrongBits := FutexState.wake futexWait.syncState futexWait.global futexMain
    (UInt32.ofNat 2) 1 .vectorClocks futexRegistry
  IO.println s!"sync:futex-nonmatching result={reprStr wrongBits.outcome} waiters={wrongBits.syncState.waiterCount}"
  let matchingBits := FutexState.wake wrongBits.syncState wrongBits.global wrongBits.threads
    (UInt32.ofNat 3) 1 .vectorClocks futexRegistry
  IO.println s!"sync:futex-matching result={reprStr matchingBits.outcome} pending={reprStr (matchingBits.callback.map (fun callback => callback.program))} waiters={matchingBits.syncState.waiterCount}"

  let (semaphoreThreads, semaphoreThread) ← match ThreadManager.createThread manager 90 with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok created => pure created
  let semaphoreGlobal ← match GlobalState.threadCreated global semaphoreThreads semaphoreThread none with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok updated => pure updated
  let semaphoreActive ← match ThreadManager.setActiveThread semaphoreThreads semaphoreThread with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let semWait := SemaphoreState.decrement { value := 0 } semaphoreGlobal semaphoreActive
    none 900 901 .vectorClocks true
  let semaphoreMain ← match ThreadManager.setActiveThread semWait.threads ThreadId.MAIN_THREAD with
    | .error error =>
      IO.println s!"sync:test-setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let semIncrement := SemaphoreState.increment semWait.syncState semWait.global
    semaphoreMain .vectorClocks semWait.callbackRegistration.toList
  IO.println s!"sync:semaphore-increment result={reprStr semIncrement.outcome} value={semIncrement.syncState.value.toNat} pending={reprStr (semIncrement.callback.map (fun callback => callback.program))} active={semIncrement.threads.activeThread.toNat}"
