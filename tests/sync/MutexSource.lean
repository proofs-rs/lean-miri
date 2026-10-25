import Miri.Concurrency.Sync

open Miri.Concurrency

private def remoteClock : VClock :=
  VClock.newWithIndex (VectorIdx.ofU32 1 (by decide))
    (VTimestamp.ofPacked 6 (by decide))

private def acquiredClock (state : GlobalState) : Option Nat := do
  let clocks ← state.vectorClocks.head?
  let index ← (VectorIdx.ofNat 1).toOption
  pure (clocks.clock.index index).time

private def mainClock (state : GlobalState) : Option Nat := do
  let clocks ← state.vectorClocks.head?
  let index := VectorIdx.ofU32 0 (by decide)
  pure (clocks.clock.index index).time

private def mutexResultCode (result : Except SyncError MutexUnlockResult) : String :=
  match result with
  | .error _ => "error"
  | .ok .returnedNone => "none"
  | .ok (.returnedSome count) => s!"some {count}"

def main : IO Unit := do
  let manager := ThreadManager.initial false
  let global := GlobalState.initial true false
  let first := MutexState.lock { clock := remoteClock } global manager .vectorClocks
  let second := MutexState.lock first.syncState first.global manager .vectorClocks
  IO.println s!"sync:mutex-lock owner={reprStr (first.syncState.owner.map ThreadId.toNat)} count={second.syncState.lockCount} acquired={reprStr (acquiredClock second.global)}"

  let (withChild, child) ← match ThreadManager.createThread manager 7 with
    | .error error =>
      IO.println s!"sync:mutex-owner-check=setup-error:{reprStr error}"
      return
    | .ok created => pure created
  let childManager ← match ThreadManager.setActiveThread withChild child with
    | .error error =>
      IO.println s!"sync:mutex-owner-check=setup-error:{reprStr error}"
      return
    | .ok (updated, _) => pure updated
  let wrongOwner := MutexState.lock
    { owner := some ThreadId.MAIN_THREAD, lockCount := 1 }
    global childManager .none
  let ownerCheck := match wrongOwner.outcome with
    | .error (.mutexSourceAssertion _) => "reject"
    | _ => "accept"
  IO.println s!"sync:mutex-owner-check={ownerCheck}"
  let wrongUnlock := MutexState.unlock
    { owner := some ThreadId.MAIN_THREAD, lockCount := 1 }
    global childManager .none
  IO.println s!"sync:mutex-wrong-owner-unlock={mutexResultCode wrongUnlock.outcome}"

  let overflow := MutexState.lock
    { owner := some ThreadId.MAIN_THREAD, lockCount := 18446744073709551615 }
    global manager .none 64
  let overflowCheck := match overflow.outcome with
    | .error (.mutexLockCountOverflow 64) => "reject"
    | _ => "accept"
  IO.println s!"sync:mutex-overflow={overflowCheck}"

  let mainIndex := VectorIdx.ofU32 0 (by decide)
  let timeFour := VTimestamp.ofPacked 8 (by decide)
  let globalAtFour := { global with vectorClocks :=
    [{ ThreadClockSet.default with clock := VClock.newWithIndex mainIndex timeFour }] }
  let unlockInitial : MutexState := { owner := some ThreadId.MAIN_THREAD, lockCount := 2 }
  let inner := MutexState.unlock unlockInitial globalAtFour manager .vectorClocks
  IO.println s!"sync:mutex-unlock-inner={mutexResultCode inner.outcome}:{inner.syncState.lockCount}:{reprStr (mainClock inner.global)}"
  let outer := MutexState.unlock inner.syncState inner.global manager .vectorClocks
  let releasedMutexClock := (outer.syncState.clock.index mainIndex).time
  IO.println s!"sync:mutex-unlock-outer={mutexResultCode outer.outcome}:{reprStr (outer.syncState.owner.map ThreadId.toNat)}:{releasedMutexClock}:{reprStr (mainClock outer.global)}"
