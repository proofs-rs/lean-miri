import Miri.Concurrency.GlobalState

open Miri.Concurrency

private def ix0 : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def ix1 : VectorIdx := VectorIdx.ofU32 1 (by decide)

private def timestamp (time : Fin 2147483648) : VTimestamp :=
  VTimestamp.ofPacked (2 * time.val) (by have h := time.isLt; omega)

private def t0 : VTimestamp := timestamp ⟨0, by decide⟩
private def t1 : VTimestamp := timestamp ⟨1, by decide⟩
private def t2 : VTimestamp := timestamp ⟨2, by decide⟩
private def t3 : VTimestamp := timestamp ⟨3, by decide⟩

private def clock (t0 t1 : VTimestamp) : VClock :=
  VClock.fromTimestamps [t0, t1]

private def clockSet (happensBefore : VClock) : ThreadClockSet :=
  { ThreadClockSet.default with clock := happensBefore }

private def timePair (value : VClock) : String :=
  s!"{(value.index ix0).time},{(value.index ix1).time}"

private def reuseCode (state : GlobalState) : String :=
  match GlobalState.reusableCandidates state with
  | [] => "none"
  | [index] => toString index.toNat
  | indices => String.intercalate "," (indices.map fun index => toString index.toNat)

def main : IO Unit := do
  let base := GlobalState.initial false false
  let safe := { base with
    vectorClocks := [clockSet (clock t0 t2), clockSet (clock t0 t2)]
    vectorInfo := [ThreadId.MAIN_THREAD, ThreadId.ofU32 1 (by decide)]
    reuseCandidates := [ix1] }
  IO.println s!"reuse:safe:{reuseCode safe}"

  let blocked := { base with
    vectorClocks := [clockSet (clock t0 t1), clockSet (clock t0 t2)]
    vectorInfo := [ThreadId.MAIN_THREAD, ThreadId.ofU32 1 (by decide)]
    reuseCandidates := [ix1] }
  IO.println s!"reuse:blocked:{reuseCode blocked}"

  let thread := { ThreadClockSet.default with
    clock := clock t1 t0
    fenceAcquire := clock t0 t1 }
  let global := { base with
    multiThreaded := true
    vectorClocks := [thread]
    lastScFence := clock t0 t2
    lastScWritePerThread := clock t0 t1 }
  let manager := ThreadManager.initial false
  match GlobalState.atomicFence global manager .SeqCst with
  | .error _ => IO.println "sc:fence:error"
  | .ok after =>
    match after.vectorClocks with
    | [] => IO.println "sc:fence:missing-clock"
    | thread :: _ =>
      IO.println s!"sc:fence:clock=[{timePair thread.clock}]:release=[{timePair thread.fenceRelease}]:write=[{timePair thread.writeSeqCst}]:last=[{timePair after.lastScFence}]"

  let manager := ThreadManager.initial false
  let enabled := { base with
    multiThreaded := true
    vectorClocks := [clockSet (clock t1 t0)] }
  let advanceBody : VectorIdx → ThreadClockSet → Unit →
      SyncOperationBodyResult Unit ClockError Unit :=
    fun index clocks _ =>
    match clocks.incrementClock index with
    | .error error => { clocks := clocks, external := (), outcome := .error error }
    | .ok next => { clocks := next, external := (), outcome := .ok (true, ()) }
  let afterEnabled := enabled.maybePerformSyncOperation manager () advanceBody
  IO.println s!"sync-op:enabled:{match afterEnabled.global.vectorClocks with | [clocks] => timePair clocks.clock | _ => "missing"}"

  let skipped := base
  let skippedBody : VectorIdx → ThreadClockSet → Unit →
      SyncOperationBodyResult Unit String Unit :=
    fun _ clocks _ =>
    { clocks := clocks, external := (), outcome := .ok (true, ()) }
  let afterSkipped := skipped.maybePerformSyncOperation manager () skippedBody
  IO.println s!"sync-op:single:called:{match afterSkipped.outcome with | .ok none => "0" | _ => "1"}:clock:{match afterSkipped.global.vectorClocks with | [clocks] => timePair clocks.clock | _ => "missing"}"

  let noIncrementBody : VectorIdx → ThreadClockSet → Unit →
      SyncOperationBodyResult Unit String Unit :=
    fun _ clocks _ =>
    { clocks := clocks, external := (), outcome := .ok (false, ()) }
  let afterNoIncrement := enabled.maybePerformSyncOperation manager () noIncrementBody
  IO.println s!"sync-op:no-increment:{match afterNoIncrement.global.vectorClocks with | [clocks] => timePair clocks.clock | _ => "missing"}"

  let errorBody : VectorIdx → ThreadClockSet → Unit →
      SyncOperationBodyResult Unit String Unit :=
    fun index clocks _ =>
    match clocks.incrementClock index with
    | .error _ => { clocks := clocks, external := (), outcome := .error "clock-error" }
    | .ok next => { clocks := next, external := (), outcome := .error "body-error" }
  let afterError := enabled.maybePerformSyncOperation manager () errorBody
  IO.println s!"sync-op:error:{match afterError.outcome with | .error (.inr _) => "error" | _ => "other"}:{match afterError.global.vectorClocks with | [clocks] => timePair clocks.clock | _ => "missing"}"
