import Miri.Concurrency.AtomicDispatch
open Miri.ABI Miri.Memory Miri.Concurrency
private def must (result : Except E A) : IO A :=
  match result with | .ok value => pure value | .error _ => throw (IO.userError "fixture setup")
private def state : IO (AtomicState Nat) := do
  let time ← must (VTimestamp.ofTime 5)
  let initial := GlobalState.initial false true
  let global := { initial with
    multiThreaded := true
    vectorClocks := [{ ThreadClockSet.default with clock := VClock.newWithIndex (VectorIdx.ofU32 0 (by decide)) time }]
    lastScFence := VClock.newWithIndex (VectorIdx.ofU32 1 (by decide)) time }
  pure { global
         allocation := VClockAlloc.newAllocation (ByteSize.ofU64 4 (by decide)) VTimestamp.ZERO (VectorIdx.ofU32 0 (by decide))
         weakMemoryAllocation := none }
private def readMarker (state : AtomicState Nat) (threads : ThreadManager) : IO Nat := do
  let (_, clocks) ← must (state.global.activeThreadState threads)
  pure (clocks.readSeqCst.index (VectorIdx.ofU32 1 (by decide))).time

def main : IO Unit := do
  let threads := ThreadManager.initial false
  let range : AllocRange := ⟨Size.ZERO, Size.ofBytes 4⟩
  for payload in [0,1,2] do
    for sc in [false,true] do
      let initial ← state
      let initial := if payload == 0 then initial else
        {initial with weakMemoryAllocation := some StoreBufferAlloc.newAllocation}
      let initial ← if payload == 2 then do
        let stored := atomicStoreState initial threads range .Relaxed 42 (some 0)
        let _ ← must stored.outcome
        pure stored.state
        else pure initial
      let prepared := prepareBufferedAtomicRead initial threads range (if sc then .SeqCst else .Relaxed) 42
      let plan ← must prepared.outcome
      let label := match plan with | .ready _ => "ready" | .select _ _ => "select"
      IO.println s!"{payload}|{sc}|{← readMarker prepared.state threads}|{label}"
