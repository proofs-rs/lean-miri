import Miri.Concurrency.AtomicDispatch

open Miri.ABI Miri.Memory Miri.Concurrency

private def ix0 : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def ix1 : VectorIdx := VectorIdx.ofU32 1 (by decide)
private def accessRange : AllocRange := ⟨Size.ZERO, Size.ofBytes 4⟩

private def timestamp (n : Nat) : VTimestamp :=
  (VTimestamp.ofTime n).toOption.getD VTimestamp.ZERO

private def initial (weakMemory : Bool) : AtomicState Nat :=
  let base := GlobalState.initial false weakMemory
  let global := { base with
    multiThreaded := false
    lastScFence := VClock.newWithIndex ix1 (timestamp 7) }
  { global := global
    allocation := VClockAlloc.newAllocation
      (ByteSize.ofU64 4 (by decide)) VTimestamp.ZERO ix0
    weakMemoryAllocation := none }

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let threads := ThreadManager.initial false

  -- A failed SC CAS with an installed but inactive vector-clock backend still
  -- performs the source SC-read mark even when weak memory is disabled and the
  -- allocation has no StoreBufferAlloc payload.
  let noBuffer := atomicCompareExchangeFailureState (initial false) threads
    accessRange .SeqCst
  check noBuffer.outcome.isOk "inactive failed-CAS SC tail unexpectedly failed"
  let (_, afterNoBuffer) ← match noBuffer.state.global.activeThreadState threads with
    | .ok active => pure active
    | .error _ => throw (IO.userError "failed-CAS active vector clock disappeared")
  check ((afterNoBuffer.readSeqCst.index ix1).time == 7)
    "failed-CAS SC-read mark was lost without weak-memory state"

  -- A retained buffer is read from its latest modification-order entry and
  -- commits the per-thread load timestamp plus its SeqCst bit.
  let freshBuffer := (StoreBufferAlloc.newAllocation : StoreBufferAlloc Nat)
    |>.getOrCreateStoreBuffer accessRange (some 42)
  let bufferedState := { initial true with
    weakMemoryAllocation := some freshBuffer.allocation }
  let buffered := atomicCompareExchangeFailureState bufferedState threads
    accessRange .SeqCst
  check buffered.outcome.isOk "inactive failed-CAS latest-buffer read failed"
  let some buffers := buffered.state.weakMemoryAllocation
    | throw (IO.userError "latest-read update dropped the retained buffer")
  let handle ← match buffers.getStoreBuffer accessRange with
    | .ok (some handle) => pure handle
    | _ => throw (IO.userError "retained exact-range buffer disappeared")
  check (handle.buffer.last.val == some 42) "latest buffer value changed"
  check (handle.buffer.last.loadInfo.timestampFor? ix0).isSome
    "failed-CAS path did not record its latest retained-buffer read"
  check handle.buffer.last.loadInfo.scLoaded
    "failed-CAS SeqCst buffer read did not retain its SC marker"

  IO.println "atomic-cas-failure-state:inactive-sc-read-and-latest-buffer:PASS"
