import Miri.Concurrency.Sync

open Miri.Concurrency

private def clockAtOne (state : GlobalState) : Option Nat := do
  let clocks ← state.vectorClocks.head?
  let index ← (VectorIdx.ofNat 1).toOption
  pure (clocks.clock.index index).time

private def readerCountCode (readers : List (ThreadId × Nat))
    (thread : ThreadId) : String :=
  match readers.filter (fun entry => entry.1 == thread) with
  | [(_, count)] => toString count
  | _ => "invalid"

def main : IO Unit := do
  let manager := ThreadManager.initial false
  let global := GlobalState.initial true false
  let clockFour := VClock.newWithIndex (VectorIdx.ofU32 1 (by decide))
    (VTimestamp.ofPacked 8 (by decide))
  let reader := RwLockState.readerLock { clockUnlocked := clockFour }
    global manager .vectorClocks
  IO.println s!"sync:rwlock-reader-lock readers={readerCountCode reader.syncState.readers manager.activeThread} acquired={reprStr (clockAtOne reader.global)}"

  let clockFive := VClock.newWithIndex (VectorIdx.ofU32 1 (by decide))
    (VTimestamp.ofPacked 10 (by decide))
  let writer := RwLockState.writerLock { clockUnlocked := clockFive }
    global manager .vectorClocks
  IO.println s!"sync:rwlock-writer-lock owner={reprStr (writer.syncState.writer.map ThreadId.toNat)} acquired={reprStr (clockAtOne writer.global)}"
